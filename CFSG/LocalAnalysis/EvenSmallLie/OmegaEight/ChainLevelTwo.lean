module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Lift
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainAbel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G] {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p : Fin 6 → G} {u : Fin 6 → G}

theorem UData.card_U_ge [Finite G]
    (hS : Setup ε t L U Q P a ψ p) (hu : UData ε U Q ψ u) : 4096 ≤ Nat.card U := by
  classical
  have hR := hS.rad
  have hUN : U ≤ normalizer (Q : Set G) := fun x hx => hR.P_le_normalizer (hR.U_le_P hx)
  let φ : U →* Equiv.Perm V6 := hR.linHom.comp (Subgroup.inclusion hUN)
  have hφ : ∀ (x : U) v, φ x v = lin ψ x v := fun x v => rfl
  have hker : 64 ≤ Nat.card φ.ker := by
    let f : Q → φ.ker := fun q => ⟨⟨q, hR.Q_le_U q.2⟩, MonoidHom.mem_ker.2 (Equiv.ext fun v => by
      rw [hφ]; exact hR.lin_of_mem_Q q.2 v)⟩
    have hf : Function.Injective f := fun q q' h => by
      have := congrArg (fun x : φ.ker => ((x : U) : G)) h
      exact Subtype.ext this
    have := Nat.card_le_card_of_injective f hf
    rwa [hR.card_Q] at this
  have hrange : 64 ≤ Nat.card φ.range := by
    choose x hxU hx using fun i : Fin 64 => hu.exists_mem_U hR i.isLt
    let f : Fin 64 → φ.range := fun i => ⟨φ ⟨x i, hxU i⟩, ⟨_, rfl⟩⟩
    have hf : Function.Injective f := by
      intro i j h
      have h' : ∀ v, s0Mat ε i *ᵥ v = s0Mat ε j *ᵥ v := fun v => by
        rw [← hx i v, ← hx j v]
        exact congrFun (congrArg (fun σ : φ.range => ((σ : Equiv.Perm V6) : V6 → V6)) h) v
      exact Fin.ext (eq_of_mulVec_eq ε i.isLt j.isLt h')
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_fin] at this
  have hcard : Nat.card U = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard]
  calc 4096 = 64 * 64 := by norm_num
    _ ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul hker hrange

theorem card_le_of_odd_relIndex [Finite G] {T B C : Subgroup G} (hT : IsPGroup 2 T)
    (hB : IsPGroup 2 B) (hBC : B ≤ C) (hodd : Odd (T.relIndex C)) :
    Nat.card B ≤ Nat.card (T ⊓ C : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  obtain ⟨m, hm⟩ := (hT.to_le (inf_le_left : T ⊓ C ≤ T)).exists_card_eq
  have h1 := relIndex_mul_card (H := T) (K := C)
  have h2 : Nat.card B ∣ Nat.card C := Subgroup.card_dvd_of_le hBC
  rw [← h1, hn, hm] at h2
  have hcop : Nat.Coprime (2 ^ n) (T.relIndex C) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd)
  have h3 := hcop.dvd_of_dvd_mul_left h2
  rw [hn, hm]
  exact Nat.le_of_dvd (by positivity) h3

theorem mul_inv_mem_Q_of_lin_eq (hS : Setup ε t L U Q P a ψ p) {x y : G} (hx : x ∈ P)
    (hy : y ∈ P) (h : ∀ v, lin ψ x v = lin ψ y v) : x * y⁻¹ ∈ Q := by
  have hR := hS.rad
  have hxN := hR.P_le_normalizer hx
  have hyN := hR.P_le_normalizer hy
  refine hS.mem_Q_of_mem_P (mul_mem hx (inv_mem hy)) (mem_centralizer_iff.2 fun q hq => ?_)
  obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
  have h1 : lin ψ (x * y⁻¹) v = v := by
    rw [hR.lin_mul hxN (inv_mem hyN), h, hR.lin_inv hyN]
  have h2 := (hR.lin_eq_iff (mul_mem hxN (inv_mem hyN)) v v).1 h1
  calc ψ v * (x * y⁻¹) = x * y⁻¹ * ψ v * (x * y⁻¹)⁻¹ * (x * y⁻¹) := by rw [h2]
    _ = x * y⁻¹ * ψ v := by group

theorem center_s0 (ε : Eps) {i : ℕ} (hi : i < 64)
    (h : ∀ j < 64, tabGet (mulTab ε) j i = tabGet (mulTab ε) i j) : i = 0 ∨ i = zIdx ε := by
  have hc := centerCheck_spec ε
  simp only [centerCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at hc
  rcases hc i hi with (h1 | h1) | h1
  · exfalso
    have : ((List.range 64).all fun j =>
        tabGet (mulTab ε) i j == tabGet (mulTab ε) j i) = true := by
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
      exact fun j hj => (h j hj).symm
    rw [this] at h1
    exact Bool.noConfusion h1
  · exact Or.inl h1
  · exact Or.inr h1

namespace Config

variable {k : ℕ} {A : Subgroup G} (hS : Setup ε t L U Q P a ψ p) (hC : Config t Q P k A)
include hS hC

theorem not_t_mem_A : t ∉ A := by
  have := hC.conj_not_mem_A hS 1
  simpa using this

theorem relIndex_A_At [Finite G] : A.relIndex (A ⊔ zpowers t) = 2 := by
  have htA := hC.not_t_mem_A hS
  rw [relIndex_eq_two_iff]
  refine ⟨t, mem_sup_right (mem_zpowers t), fun b hb => ?_⟩
  obtain ⟨c, hc, rfl | rfl⟩ := hC.mem_At hS hb
  · exact Or.inr ⟨hc, fun h => htA (by simpa using mul_mem (inv_mem hc) h)⟩
  · refine Or.inl ⟨by rw [mul_assoc, hS.shape.mul_self, mul_one]; exact hc, fun h => htA ?_⟩
    simpa using mul_mem (inv_mem hc) h

theorem exists_U_of_mem_T [Finite G] {x : G} (hx : x ∈ A ⊔ (U ⊔ zpowers t)) :
    x ∈ normalizer (Q : Set G) ∧ ∃ y ∈ U, ∀ v, lin ψ x v = lin ψ y v := by
  have hR := hS.rad
  have htN : t ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_mem fun q hq => by
    rw [← hS.shape.commute_of_mem (hR.Q_le_L hq), mul_inv_cancel_right]
    exact hq
  have htl : ∀ v, lin ψ t v = v := fun v => by
    rw [hR.lin_eq_iff htN, ← hS.shape.commute_of_mem (hR.Q_le_L (hR.ψ_mem v)),
      mul_inv_cancel_right]
  obtain ⟨b, hb, y, hy, rfl | rfl⟩ := hC.mem_T hS hx
  · have hbN := hC.mem_normalizer_Q_of_mem_A hb
    have hyN := hR.P_le_normalizer (hR.U_le_P hy)
    refine ⟨mul_mem hbN hyN, y, hy, fun v => ?_⟩
    rw [hR.lin_mul hbN hyN, hC.lin_of_mem_A hS hb]
  · have hbN := hC.mem_normalizer_Q_of_mem_A hb
    have hyN := hR.P_le_normalizer (hR.U_le_P hy)
    refine ⟨mul_mem (mul_mem hbN hyN) htN, y, hy, fun v => ?_⟩
    rw [hR.lin_mul (mul_mem hbN hyN) htN, htl, hR.lin_mul hbN hyN, hC.lin_of_mem_A hS hb]

theorem card_centralizer_le [Finite G] (hu : UData ε U Q ψ u)
    {w : G} (hwN : w ∈ normalizer (Q : Set G)) {i : ℕ} (hi : i < 64)
    (hwi : ∀ v, lin ψ w v = s0Mat ε i *ᵥ v) :
    Nat.card ((A ⊔ (U ⊔ zpowers t)) ⊓ centralizer ({w} : Set G) : Subgroup G) ≤
      2 * Nat.card (A ⊓ centralizer ({w} : Set G) : Subgroup G) *
        ((Finset.range 64).filter fun j => tabGet (mulTab ε) j i = tabGet (mulTab ε) i j).card := by
  classical
  have hR := hS.rad
  set K : Subgroup G := (A ⊔ (U ⊔ zpowers t)) ⊓ centralizer ({w} : Set G) with hK
  have hKN : K ≤ normalizer (Q : Set G) := fun x hx => (hC.exists_U_of_mem_T hS hx.1).1
  let φ : K →* Equiv.Perm V6 := hR.linHom.comp (Subgroup.inclusion hKN)
  have hφ : ∀ (x : K) v, φ x v = lin ψ x v := fun x v => rfl
  have hS0 : ∀ x : K, ∃ j < 64, (∀ v, lin ψ x v = s0Mat ε j *ᵥ v) ∧
      tabGet (mulTab ε) j i = tabGet (mulTab ε) i j := by
    intro x
    obtain ⟨hxN, y, hy, hxy⟩ := hC.exists_U_of_mem_T hS x.2.1
    obtain ⟨j, hj, hyj⟩ := hu.exists_s0 hR hy
    refine ⟨j, hj, fun v => by rw [hxy, hyj], ?_⟩
    refine tab_comm_of_commute ε hj hi (Matrix.ext_iff_mulVec.2 fun v => ?_)
    have hc : (x : G) * w = w * x := mem_centralizer_singleton_iff.1 x.2.2
    have e1 : lin ψ ((x : G) * w) v = (s0Mat ε j * s0Mat ε i) *ᵥ v := by
      rw [hR.lin_mul hxN hwN, hwi, hxy, hyj, mulVec_mulVec]
    have e2 : lin ψ (w * x) v = (s0Mat ε i * s0Mat ε j) *ᵥ v := by
      rw [hR.lin_mul hwN hxN, hxy, hyj, hwi, mulVec_mulVec]
    rw [← e1, ← e2, hc]
  choose f hf64 hfv hfc using hS0
  have hrange : Nat.card φ.range ≤
      ((Finset.range 64).filter fun j => tabGet (mulTab ε) j i = tabGet (mulTab ε) i j).card := by
    have : ∀ σ : φ.range, ∃ j : ((Finset.range 64).filter
        fun j => tabGet (mulTab ε) j i = tabGet (mulTab ε) i j), ∀ v,
        (σ : Equiv.Perm V6) v = s0Mat ε j *ᵥ v := by
      rintro ⟨σ, x, rfl⟩
      exact ⟨⟨f x, Finset.mem_filter.2 ⟨Finset.mem_range.2 (hf64 x), hfc x⟩⟩,
        fun v => by rw [hφ]; exact hfv x v⟩
    choose g hg using this
    have hinj : Function.Injective g := by
      intro σ τ h
      exact Subtype.ext (Equiv.ext fun v => by rw [hg σ v, hg τ v, h])
    have := Nat.card_le_card_of_injective g hinj
    rwa [Nat.card_eq_finsetCard] at this
  have hker : Nat.card φ.ker ≤ 2 * Nat.card (A ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    set K' : Subgroup G := (A ⊔ zpowers t) ⊓ centralizer ({w} : Set G)
    have hmem : ∀ x : φ.ker, ((x : K) : G) ∈ K' := by
      intro x
      have h1 : ∀ v, lin ψ (x : K) v = v := fun v => by
        rw [← hφ, MonoidHom.mem_ker.1 x.2]; rfl
      refine ⟨hC.mem_At_of_centralizer_Q hS (x : K).2.1 fun q hq => ?_, (x : K).2.2⟩
      obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
      have := (hR.lin_eq_iff (hKN (x : K).2) v v).1 (h1 v)
      calc ((x : K) : G) * ψ v = ((x : K) : G) * ψ v * ((x : K) : G)⁻¹ * (x : K) := by group
        _ = ψ v * (x : K) := by rw [this]
    let e : φ.ker → K' := fun x => ⟨_, hmem x⟩
    have he : Function.Injective e := fun x y h => by
      have h' : ((x : K) : G) = ((y : K) : G) := congrArg (fun z : K' => (z : G)) h
      exact Subtype.ext (Subtype.ext h')
    have h1 := Nat.card_le_card_of_injective e he
    have h2 := relIndex_mul_card (H := A) (K := K')
    have h3 : A ⊓ K' = A ⊓ centralizer ({w} : Set G) := by
      ext x
      simp only [K', mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, mem_sup_left h.1, h.2⟩⟩
    have h4 : A.relIndex K' ≤ 2 :=
      (relIndex_le_of_le_right inf_le_left (by rw [hC.relIndex_A_At hS]; norm_num)).trans
        (hC.relIndex_A_At hS).le
    rw [h3] at h2
    calc Nat.card φ.ker ≤ Nat.card K' := h1
      _ = A.relIndex K' * Nat.card (A ⊓ centralizer ({w} : Set G) : Subgroup G) := h2.symm
      _ ≤ 2 * Nat.card (A ⊓ centralizer ({w} : Set G) : Subgroup G) := Nat.mul_le_mul_right _ h4
  have hcard : Nat.card K = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard]
  exact Nat.mul_le_mul hker hrange

end Config

theorem levelTwoKill_minus [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x) (hS : Setup .minus t L U Q P a ψ p)
    (hu : UData .minus U Q ψ u)
    (hk : ∃ k ∈ P, (∀ v, lin ψ k v = toMat 6 6 kRows *ᵥ v) ∧ k ^ 4 = 1) :
    LevelTwoKill t Q P := by
  intro A hC hinv hN
  have hR := hS.rad
  have hT : Terminal t P 2 A := Or.inl ⟨hinv, hN⟩
  obtain ⟨g, hgM, hodd⟩ := hC.exists_conj_mem_AU hS hG hnab hT
  obtain ⟨b, hb, h, hh, hbh, hhQ, -⟩ := hC.conj_decomp hS hgM
  have hDK : U ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le (hR.U_le_L.trans hS.shape.le_centralizer)
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hTH : 8192 ≤ Nat.card ((A ⊔ (U ⊔ zpowers t)) ⊓
      centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) := by
    set B : Subgroup G := (U ⊔ zpowers t).map (MulAut.conj g).toMonoidHom
    have hBC : B ≤ centralizer ({g * t * g⁻¹} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hDK hx)
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
        _ = g * (t * x) * g⁻¹ := by rw [hxt]
        _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
    have hB2 : IsPGroup 2 B := (hS.shape.isPGroup_sup hR.U_le_L hR.U_pgroup).map _
    have hle := card_le_of_odd_relIndex (hC.isPGroup_T hS) hB2 hBC hodd
    have hcB : Nat.card B = Nat.card (U ⊔ zpowers t : Subgroup G) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hTHc : Nat.card (U ⊔ zpowers t : Subgroup G) = 2 * Nat.card U := by
      have := relIndex_mul_card (H := U) (K := U ⊔ zpowers t)
      rw [relIndex_U_TH hS, inf_of_le_left le_sup_left] at this
      exact this.symm
    have hU := hu.card_U_ge hS
    omega
  obtain ⟨i, hi, hhi⟩ := hu.exists_s0 hR hh
  have hhN := hR.P_le_normalizer (hR.U_le_P hh)
  have hbN := hC.mem_normalizer_Q_of_mem_A hb
  have hwN : g * t * g⁻¹ ∈ normalizer (Q : Set G) := by rw [hbh]; exact mul_mem hbN hhN
  have hwi : ∀ v, lin ψ (g * t * g⁻¹) v = s0Mat .minus i *ᵥ v := fun v => by
    rw [hbh, hR.lin_mul hbN hhN, hC.lin_of_mem_A hS hb, hhi]
  have hcent := hC.card_centralizer_le hS hu hwN hi hwi
  have hD := two_mul_card_le (hu.abelBound hS) hS.shape.mul_self (g := g)
    (D := A ⊓ centralizer ({g * t * g⁻¹} : Set G)) (hC.isPGroup_A.to_le inf_le_left)
    (fun x hx y hy => hC.level.comm x hx.1 y hy.1)
    (fun d hd => mem_centralizer_singleton_iff.1 hd.2) (fun hw => hC.conj_not_mem_A hS g hw.1)
  set c := ((Finset.range 64).filter
    fun j => tabGet (mulTab .minus) j i = tabGet (mulTab .minus) i j).card with hc
  have hc64 : 64 ≤ c := by
    have h1 : 2 * Nat.card (A ⊓ centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) * c ≤ 128 * c :=
      Nat.mul_le_mul_right _ hD
    omega
  have hcentral : ∀ j < 64, tabGet (mulTab .minus) j i = tabGet (mulTab .minus) i j := by
    have hcard : ((Finset.range 64).filter
        fun j => tabGet (mulTab .minus) j i = tabGet (mulTab .minus) i j).card =
        (Finset.range 64).card := by
      refine le_antisymm (Finset.card_filter_le _ _) ?_
      rw [Finset.card_range]
      exact hc64
    intro j hj
    exact Finset.filter_card_eq hcard j (Finset.mem_range.2 hj)
  rcases center_s0 .minus hi hcentral with rfl | rfl
  ·
    apply hhQ
    refine hS.mem_Q_of_mem_P (hR.U_le_P hh) (mem_centralizer_iff.2 fun q hq => ?_)
    obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
    have h1 := (hR.lin_eq_iff hhN v v).1 (by rw [hhi, s0Mat_zero, one_mulVec])
    calc ψ v * h = h * ψ v * h⁻¹ * h := by rw [h1]
      _ = h * ψ v := by group
  ·
    obtain ⟨k, hkP, hkl, hk4⟩ := hk
    have hkN := hR.P_le_normalizer hkP
    have hkk : ∀ v, lin ψ h v = lin ψ (k * k) v := fun v => by
      rw [hhi, hR.lin_mul hkN hkN, hkl, hkl, mulVec_mulVec, kRows_sq, s0Mat]
    have hq1 := mul_inv_mem_Q_of_lin_eq hS (hR.U_le_P hh) (mul_mem hkP hkP) hkk
    obtain ⟨Φ, hΦ, hrepW⟩ := exists_coord_lift (ε := .minus) hS hC.level
      (fun x hx y hy => hC.P_norm x hx y hy)
    have hk0 := hrepW kWord
    rw [← kTil_eq] at hk0
    have hkk0 : ∀ v, lin ψ k v = lin ψ (wordElt p kWord) v := fun v => by
      rw [hkl, lin_wordElt_eq hR, wordRows_kWord]
    have hq0 := mul_inv_mem_Q_of_lin_eq hS hkP (hR.wordElt_mem kWord) hkk0
    have hrepk : Rep Φ k kTil := by
      have h1 := Coord4.rep_mul (hΦ.rep_of_mem_A hC.level.comm (hC.level.Q_le hq0)) hk0
      rwa [one_mul, inv_mul_cancel_right] at h1
    have hrepkk : Rep Φ (k * k) (kTil * kTil) := Coord4.rep_mul hrepk hrepk
    have hc'A : b * (h * (k * k)⁻¹) ∈ A := mul_mem hb (hC.level.Q_le hq1)
    have hwc : g * t * g⁻¹ = b * (h * (k * k)⁻¹) * (k * k) := by rw [hbh]; group
    obtain ⟨x, hx⟩ := hΦ.surj _ hc'A
    rw [← hx] at hwc
    have hw2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
      rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, hS.shape.mul_self]
      group
    have hk4' : k * k * (k * k) = 1 := by
      rw [← hk4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have hx0 : (1 + kTil * kTil) *ᵥ x = 0 := by
      apply hΦ.inj
      have e : g * t * g⁻¹ * (g * t * g⁻¹) =
          Φ x * ((k * k) * Φ x * (k * k)⁻¹) * (k * k * (k * k)) := by
        rw [hwc]
        simp only [mul_assoc, _root_.mul_inv_rev, inv_mul_cancel_left]
      rw [hk4', mul_one, hrepkk x, ← hΦ.add, hw2] at e
      rw [add_mulVec, one_mulVec]
      exact e.symm
    have hconj : ∀ y : G, y * y = g * t * g⁻¹ → False := fun y hy => by
      apply hS.shape.not_square (g⁻¹ * y * g)
      calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
        _ = t := by rw [hy]; group
    obtain ⟨v, hv | hv⟩ := exists_sqrt x hx0
    ·
      refine hconj (Φ v * k) ?_
      have h1 : Φ x = Φ v * (k * Φ v * k⁻¹) := by
        rw [← hv, add_mulVec, one_mulVec, hΦ.add, hrepk v]
      rw [hwc, h1]
      group
    ·
      refine hconj (Φ v * t * k) ?_
      have hkt : k * t = t * k := hS.shape.commute_of_mem (hR.P_le_L hkP)
      have h1 : Φ x = Φ v * (k * Φ v * k⁻¹)⁻¹ := by
        rw [← hv, sub_mulVec, one_mulVec, sub_eq_add_neg, hΦ.add, hΦ.neg, hrepk v]
      have h2 : t * (k * Φ v * k⁻¹) * t⁻¹ = (k * Φ v * k⁻¹)⁻¹ :=
        hinv _ (by rw [hrepk v]; exact hΦ.mem _)
      have h3 : t * k * t * k = k * k := by
        rw [← hkt, mul_assoc k t t, hS.shape.mul_self, mul_one]
      rw [hwc, h1, ← h2]
      calc Φ v * t * k * (Φ v * t * k) =
          Φ v * (t * (k * Φ v * k⁻¹) * t⁻¹) * (t * k * t * k) := by group
        _ = Φ v * (t * (k * Φ v * k⁻¹) * t⁻¹) * (k * k) := by rw [h3]

end CFSG.EvenSmallLie.OmegaEight.Chain

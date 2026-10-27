module

public import CFSG.ClassicalInvolution.Q3.Sec13L94
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Core94
import CFSG.ClassicalInvolution.Asc77.AscCX8D
public import CFSG.ClassicalInvolution.AschTight.Sec7L713F

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.L94T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_one_of_isPGroup_of_odd {T N : Subgroup G} (hT : IsPGroup 2 T) (hN : Odd (Nat.card N))
    {x : G} (hxT : x ∈ T) (hxN : x ∈ N) : x = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨x, hxT⟩
  have h1 : orderOf x ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_mk (H := T) x hxT]
    exact orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk (H := N) x hxN]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
  exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)

theorem isPGroup_zpowers_of_mul_self {x : G} (hx : x * x = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hx])
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem exists_noncomm_of_isSylow2In (hΩ : HypOmegaGen Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {P : Subgroup G} (hP : IsSylow2In P L) : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  obtain ⟨-, P₀, hP₀, hP₀nab⟩ := hΩ.omega1 L hL
  have hnab₀ : ∃ x ∈ P₀, ∃ y ∈ P₀, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hP₀nab (IsMulCommutative.of_comm fun a b => Subtype.ext (h a a.2 b b.2))
  obtain ⟨k, hk, hPk⟩ := exists_conj_of_isSylow2In hP₀ hP.2.1 hP.1
  have hP₁ : IsSylow2In (conjSub k P₀) L := by
    have := hP₀.conj k
    rwa [conjSub_eq_self_of_mem hk] at this
  have hcard : Nat.card ↥(conjSub k P₀) = Nat.card ↥P := hΩ.omega3 L hL L hL _ _ hP₁ hP
  have heq : P = conjSub k P₀ := Subgroup.eq_of_le_of_card_ge hPk hcard.le
  obtain ⟨a, ha, b, hb, hab⟩ := hnab₀
  refine ⟨k * a * k⁻¹, heq ▸ conj_mem_conjSub ha, k * b * k⁻¹, heq ▸ conj_mem_conjSub hb, ?_⟩
  intro h
  apply hab
  have := congrArg (fun w => k⁻¹ * w * k) h
  simpa [mul_assoc] using this

theorem exists_dSet_of_orderOf_four (hΩ : HypOmegaGen Ω)
    (h8 : ∀ L ∈ Ω, ∀ P : Subgroup G, IsSylow2In P L → Nat.card P = 8) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {P : Subgroup G} (hP : IsPGroup 2 P) (hWP : W ≤ P) {M : Subgroup G}
    (hM : M ∈ Ω) {x : G} (hxM : x ∈ M) (hxP : x ∈ P) (hx4 : orderOf x = 4) :
    ∃ R ∈ DSet Ω W, IsSylow2In R M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  obtain ⟨R₀, hR₀, hxR₀⟩ := IsSylow2In.exists_ge hx2 (Subgroup.zpowers_le.mpr hxM)
  have hU : Subgroup.zpowers x ∈ USet Ω :=
    mem_USet_of_natCard hM hR₀ hxR₀ inferInstance
      (by rw [h8 M hM R₀ hR₀, Nat.card_zpowers, hx4])
  exact Q3CL.Thompson.exists_sylow_mem_DSet hΩ hW (hWP.trans hPQ) hM hU
    (Subgroup.zpowers_le.mpr hxM) (Subgroup.zpowers_le.mpr (hPQ hxP))

def conjRep (hΩ : HypOmegaGen Ω) {W : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) (ρ : Thompson.Rep Ω W) : Thompson.Rep Ω W where
  K := conjSub n ρ.K
  R := conjSub n ρ.R
  r := n * ρ.r * n⁻¹
  hK := hΩ.conjInvariant n ρ.K ρ.hK
  hR := Q3CL.Thompson.conjSub_mem_D hΩ ρ.hR hn
  hRK := ρ.hRK.conj n
  hr := conj_mem_conjSub ρ.hr
  hrW := fun h => ρ.hrW ((Thompson.mem_normalizer_iff_of_mem hn _).mp h)

theorem conjRep_img (hΩ : HypOmegaGen Ω) {W : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) (ρ : Thompson.Rep Ω W) :
    (conjRep hΩ hn ρ).img = Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ := by
  show Thompson.piG W (n * ρ.r * n⁻¹) = Thompson.piG W n * Thompson.piG W ρ.r *
    (Thompson.piG W n)⁻¹
  rw [Thompson.piG_mul (Subgroup.mul_mem _ hn ρ.r_mem_normalizer) (Subgroup.inv_mem _ hn),
    Thompson.piG_mul hn ρ.r_mem_normalizer, Thompson.piG_inv hn]

theorem exists_rep (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hRK : IsSylow2In R K) (hRD : R ∈ DSet Ω W) :
    ∃ ρ : Thompson.Rep Ω W, ρ.K = K ∧ ρ.R = R := by
  obtain ⟨-, -, -, -, hcard⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hRD hK hRK
  have hnle : ¬ R ≤ W := by
    intro hle
    rw [inf_eq_left.mpr hle] at hcard
    have : 0 < Nat.card ↥R := Nat.card_pos
    omega
  obtain ⟨r, hr, hrW⟩ := Set.not_subset.mp hnle
  exact ⟨⟨K, R, r, hK, hRD, hRK, hr, hrW⟩, rfl, rfl⟩

theorem exists_mGrp_conj (hP : Q3CL.PartIHypG Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {K K' : Subgroup G} {z : G} (hK : K ∈ Ω) (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hperp : KPerp Ω K = {K, K'}) (hS4 : MuIsoS4 Ω W) {RK : Subgroup G} (hRK : IsSylow2In RK K)
    (hRKD : RK ∈ DSet Ω W) {M R : Subgroup G} (hM : M ∈ Ω) (hRM : IsSylow2In R M)
    (hRD : R ∈ DSet Ω W) {r : G} (hr : IsUniqueInvolution M r) :
    ∃ n ∈ MGrp Ω W, conjSub n K = M ∧ n * z * n⁻¹ = r := by
  obtain ⟨φ, hφ⟩ := L94.exists_swap_equiv hP hW hK htrans hz hK' hne hperp hS4
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨ρ, hρK, -⟩ := exists_rep hP.hyp hW hK hRK hRKD
  obtain ⟨σ, hσM, -⟩ := exists_rep hP.hyp hW hM hRM hRD
  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem hφ (T7D.imgQ_mem ρ) (T7D.imgQ_mem σ)
  obtain ⟨n, hn, hyn⟩ := T7E.exists_mem_MGrp_of_mem_muGroup y
  have hnN : n ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hn
  have himg : Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ = σ.img := by
    rw [← hyn]
    exact congrArg Subtype.val hy
  have hKn : conjSub n K = M := by
    have := c.K_eq_of_img_eq (conjRep hP.hyp hnN ρ) σ (by rw [conjRep_img, himg])
    rw [← hρK, ← hσM]
    exact this
  refine ⟨n, hn, hKn, ?_⟩
  have h1 := hz.conj n
  rw [hKn] at h1
  exact (hr.eq h1).symm

theorem orderOf_inv_conj (y x : G) : orderOf (y⁻¹ * x * y) = orderOf x := by
  simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj y⁻¹) x

theorem conjSub_inf_eq (h : G) (A B : Subgroup G) :
    conjSub h (A ⊓ B) = conjSub h A ⊓ conjSub h B := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_inf, Subgroup.mem_inf, mem_conjSub_iff, mem_conjSub_iff]

theorem conjSub_sup_eq (h : G) (A B : Subgroup G) :
    conjSub h (A ⊔ B) = conjSub h A ⊔ conjSub h B :=
  Subgroup.map_sup _ _ _

theorem false_of_forall_conj_ne (hΩ : HypOmegaGen Ω)
    (h8 : ∀ L ∈ Ω, ∀ P : Subgroup G, IsSylow2In P L → Nat.card P = 8) {W S : Subgroup G}
    (hW : W ∈ WSet Ω) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {z e : G} (hzW : z ∈ W)
    (heW : e ∈ W) (he2 : e * e = 1) (hz2 : z * z = 1)
    (hS : IsSylow2In S (Subgroup.centralizer ({z} : Set G))) (hWS : W ≤ S)
    (hSe : S ≤ Subgroup.centralizer ({e} : Set G))
    (hT : ∀ M ∈ Ω, ∀ R : Subgroup G, IsSylow2In R M → R ∈ DSet Ω W → ∀ r : G,
      IsUniqueInvolution M r → ∃ n ∈ Subgroup.centralizer ({e} : Set G), n * z * n⁻¹ = r)
    (hZ : z ∈ zStarOf (Subgroup.centralizer ({e * z} : Set G)))
    {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hLL' : L ≠ L') {s : G}
    (hs : IsUniqueInvolution L s) (hs' : IsUniqueInvolution L' s)
    (hpair : ∀ M ∈ Ω, IsUniqueInvolution M s → M = L ∨ M = L') (hsz : s * z = z * s)
    {Q : Subgroup G} (hQ : IsSylow2In Q ((L ⊔ L') ⊓ Subgroup.centralizer ({z} : Set G)))
    (hsQ : s ∈ Q) (hQS : Q ≤ S)
    (hbad : ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ y ∈ Subgroup.centralizer ({e} : Set G),
      c * s * c⁻¹ ≠ y * z * y⁻¹) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hze : z * e = e * z := hWab z hzW e heW
  have hse : s * e = e * s := Subgroup.mem_centralizer_singleton_iff.mp (hSe (hQS hsQ))
  have hperm : ∀ y : G, y * s * y⁻¹ = s → ∀ M ∈ Ω, IsUniqueInvolution M s →
      conjSub y M = L ∨ conjSub y M = L' := fun y hy M hM hsM =>
    hpair _ (hΩ.conjInvariant y M hM) (by simpa [hy] using hsM.conj y)
  have hzs : z * s * z⁻¹ = s := by rw [← hsz, mul_inv_cancel_right]
  have hes : e * s * e⁻¹ = s := by rw [← hse, mul_inv_cancel_right]
  have hother : ∀ y : G, y * s * y⁻¹ = s →
      (conjSub y L = L → conjSub y L' = L') ∧ (conjSub y L = L' → conjSub y L' = L) := by
    intro y hy
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hperm y hy L' hL' hs' with h' | h'
      · exact absurd (conjSub_injective y (h.trans h'.symm)) hLL'
      · exact h'
    · rcases hperm y hy L' hL' hs' with h' | h'
      · exact h'
      · exact absurd (conjSub_injective y (h.trans h'.symm)) hLL'
  have hW2 : IsPGroup 2 W := hS.2.1.to_le hWS
  have F1 : ∀ M ∈ Ω, IsUniqueInvolution M s → ∀ x ∈ M, orderOf x = 4 → x * e ≠ e * x := by
    intro M hM hsM x hxM hx4 hxe
    have hWe : W ≤ Subgroup.centralizer ({e} : Set G) := fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw e heW)
    obtain ⟨P, hP, hWP⟩ := IsSylow2In.exists_ge hW2 hWe
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
    obtain ⟨y, hy, hxy⟩ := exists_conj_of_isSylow2In hP hx2
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxe))
    have hx' : y⁻¹ * x * y ∈ P := mem_conjSub_iff.mp (hxy (Subgroup.mem_zpowers x))
    have hM' : conjSub y⁻¹ M ∈ Ω := hΩ.conjInvariant y⁻¹ M hM
    have hxM' : y⁻¹ * x * y ∈ conjSub y⁻¹ M := by
      simpa using conj_mem_conjSub (n := y⁻¹) hxM
    obtain ⟨R, hRD, hRM⟩ := exists_dSet_of_orderOf_four hΩ h8 hW hP.2.1 hWP hM' hxM' hx'
      (by rw [orderOf_inv_conj]; exact hx4)
    obtain ⟨n, hn, hnz⟩ := hT _ hM' R hRM hRD _ (hsM.conj y⁻¹)
    refine hbad 1 (Subgroup.one_mem _) (y * n) (Subgroup.mul_mem _ hy hn) ?_
    calc 1 * s * 1⁻¹ = y * (y⁻¹ * s * y⁻¹⁻¹) * y⁻¹ := by group
      _ = y * n * z * (y * n)⁻¹ := by rw [← hnz]; group
  have F2 : ∀ M ∈ Ω, IsUniqueInvolution M s → ∀ x ∈ M, orderOf x = 4 → x * z ≠ z * x := by
    intro M hM hsM x hxM hx4 hxz
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
    obtain ⟨y, hy, hxy⟩ := exists_conj_of_isSylow2In hS hx2
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxz))
    have hx' : y⁻¹ * x * y ∈ S := mem_conjSub_iff.mp (hxy (Subgroup.mem_zpowers x))
    have hM' : conjSub y⁻¹ M ∈ Ω := hΩ.conjInvariant y⁻¹ M hM
    have hxM' : y⁻¹ * x * y ∈ conjSub y⁻¹ M := by
      simpa using conj_mem_conjSub (n := y⁻¹) hxM
    obtain ⟨R, hRD, hRM⟩ := exists_dSet_of_orderOf_four hΩ h8 hW hS.2.1 hWS hM' hxM' hx'
      (by rw [orderOf_inv_conj]; exact hx4)
    obtain ⟨n, hn, hnz⟩ := hT _ hM' R hRM hRD _ (hsM.conj y⁻¹)
    exact hbad y⁻¹ (Subgroup.inv_mem _ hy) n hn hnz.symm
  have hcomm_odd := Sec6Gen.comm_le_oddCore_of_twin hΩ hL hL' hLL' hs hs'
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hL hL' hLL' hs hs'
  have hL'N : L' ≤ Subgroup.normalizer (L : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hL' hL hLL'.symm hs' hs
  have hXc : ∀ y : G, y * s * y⁻¹ = s → conjSub y (L ⊔ L') = L ⊔ L' := by
    intro y hy
    rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub]
    rcases hperm y hy L hL hs with h | h
    · rw [h, (hother y hy).1 h]
    · rw [h, (hother y hy).2 h, sup_comm]
  have hzS : z ∈ S := hWS hzW
  have heS : e ∈ S := hWS heW
  have hBS : Q ⊔ Subgroup.closure ({z, e} : Set G) ≤ S :=
    sup_le hQS ((Subgroup.closure_le _).mpr (by rintro x (rfl | rfl) <;> assumption))
  have hB2 : IsPGroup 2 ↥(Q ⊔ Subgroup.closure ({z, e} : Set G)) := hS.2.1.to_le hBS
  have hXN : L ⊔ L' ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have hBN : Q ⊔ Subgroup.closure ({z, e} : Set G) ≤
      Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) := by
    refine sup_le ((hQ.1.trans inf_le_left).trans hXN) ((Subgroup.closure_le _).mpr ?_)
    rintro x (rfl | rfl)
    · exact mem_normalizer_iff_conjSub_eq.mpr (hXc x hzs)
    · exact mem_normalizer_iff_conjSub_eq.mpr (hXc x hes)
  obtain ⟨T, hTH, hBT⟩ := IsSylow2In.exists_ge hB2
    (le_sup_right : Q ⊔ Subgroup.closure ({z, e} : Set G) ≤
      (L ⊔ L') ⊔ (Q ⊔ Subgroup.closure ({z, e} : Set G)))
  have hT2 : IsPGroup 2 T := hTH.2.1
  have hQT : Q ≤ T := le_sup_left.trans hBT
  have hzT : z ∈ T := hBT (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have heT : e ∈ T := hBT (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hsT : s ∈ T := hQT hsQ
  have hX₀ : IsSylow2In (T ⊓ (L ⊔ L')) (L ⊔ L') :=
    Sec7.isSylow2In_inf_of_normal hTH le_sup_left (sup_le hXN hBN)
  have hP : IsSylow2In (T ⊓ (L ⊔ L') ⊓ L) L :=
    Sec7.isSylow2In_inf_of_normal hX₀ le_sup_left (sup_le Subgroup.le_normalizer hL'N)
  have hP' : IsSylow2In (T ⊓ (L ⊔ L') ⊓ L') L' :=
    Sec7.isSylow2In_inf_of_normal hX₀ le_sup_right (sup_le hLN Subgroup.le_normalizer)
  set P := T ⊓ (L ⊔ L') ⊓ L with hPdef
  set P' := T ⊓ (L ⊔ L') ⊓ L' with hP'def
  have hPT : P ≤ T := inf_le_left.trans inf_le_left
  have hP'T : P' ≤ T := inf_le_left.trans inf_le_left
  have hPX : P ≤ L ⊔ L' := inf_le_left.trans inf_le_right
  have hP'X : P' ≤ L ⊔ L' := inf_le_left.trans inf_le_right
  have hPL : P ≤ L := inf_le_right
  have hP'L' : P' ≤ L' := inf_le_right
  have hsP : IsUniqueInvolution P s :=
    ⟨⟨⟨hsT, Subgroup.mem_sup_left hs.mem⟩, hs.mem⟩, hs.ne_one, hs.sq,
      fun y hy hy2 => hs.unique y (hPL hy) hy2⟩
  have hsP' : IsUniqueInvolution P' s :=
    ⟨⟨⟨hsT, Subgroup.mem_sup_right hs'.mem⟩, hs'.mem⟩, hs'.ne_one, hs'.sq,
      fun y hy hy2 => hs'.unique y (hP'L' hy) hy2⟩
  have hnab := exists_noncomm_of_isSylow2In hΩ hL hP
  have hnab' := exists_noncomm_of_isSylow2In hΩ hL' hP'
  have hcommPP' : ∀ x ∈ P, ∀ y ∈ P', x * y = y * x := by
    intro x hx y hy
    have hc : x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf L := by
      have := hcomm_odd (Subgroup.commutator_mem_commutator (hPL hx) (hP'L' hy))
      rw [commutatorElement_def] at this
      exact this.1
    have hcT : x * y * x⁻¹ * y⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem (T.mul_mem (hPT hx) (hP'T hy)) (T.inv_mem (hPT hx))) (T.inv_mem (hP'T hy))
    have h1 := eq_one_of_isPGroup_of_odd hT2 (oddCoreOf_odd_natCard L) hcT hc
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hinfPP' : ∀ w ∈ P, w ∈ P' → w = 1 ∨ w = s := by
    intro w hw hw'
    by_cases hw2 : w * w = 1
    · exact hs.unique w (hPL hw) hw2
    · exfalso
      have h4 := PhilipHall.Frame.TwinPerp23.F94.orderOf_eq_four_of_sq_q8 (h8 L hL P hP) hnab hw hw2
      obtain ⟨h1, -⟩ := hΩ.omega4 L hL L' hL' hLL'
      have hdvd : 2 ^ 2 ∣ Nat.card ↥(L ⊓ L') := by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
        exact Subgroup.orderOf_dvd_natCard _ ⟨hPL hw, hP'L' hw'⟩
      have hne0 : Nat.card ↥(L ⊓ L') ≠ 0 := Nat.card_pos.ne'
      have := (padicValNat_dvd_iff_le hne0).mp hdvd
      omega
  have hconjP : ∀ y : G, y ∈ T → y * s * y⁻¹ = s → ∀ M : Subgroup G,
      conjSub y (T ⊓ (L ⊔ L') ⊓ M) = T ⊓ (L ⊔ L') ⊓ conjSub y M := by
    intro y hyT hy M
    rw [conjSub_inf_eq, conjSub_inf_eq, conjSub_eq_self_of_mem hyT, hXc y hy]
  have hswap : ∀ y : G, y ∈ T → y * s * y⁻¹ = s →
      (conjSub y P = P ∧ conjSub y P' = P') ∨ (conjSub y P = P' ∧ conjSub y P' = P) := by
    intro y hyT hy
    rw [hPdef, hP'def, hconjP y hyT hy, hconjP y hyT hy]
    rcases hperm y hy L hL hs with h | h
    · left
      rw [h, (hother y hy).1 h]
      exact ⟨rfl, rfl⟩
    · right
      rw [h, (hother y hy).2 h]
      exact ⟨rfl, rfl⟩
  have hPP'T : P ⊔ P' ≤ T := sup_le hPT hP'T
  have hQeq : T ⊓ ((L ⊔ L') ⊓ Subgroup.centralizer ({z} : Set G)) = Q :=
    hQ.2.2 _ inf_le_right (hT2.to_le inf_le_left) (le_inf hQT hQ.1)
  have hV : ∀ d ∈ P ⊔ P', d * z = z * d → d * e = e * d := by
    intro d hd hdz
    have hdQ : d ∈ Q := hQeq ▸ ⟨hPP'T hd, sup_le hPX hP'X hd,
      Subgroup.mem_centralizer_singleton_iff.mpr hdz⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSe (hQS hdQ))
  have F3 : ∀ d ∈ P ⊔ P', d * (e * z) = (e * z) * d → d * z = z * d := fun d hd hde =>
    CX.comm_of_mem_zStarOf hT2 hzT (hPP'T hd) hZ (by rw [← mul_assoc, hze, mul_assoc]) hde
  exact PhilipHall.Frame.TwinPerp23.F94.core_false hsP hsP' (h8 L hL P hP) (h8 L' hL' P' hP')
    hnab hnab' hcommPP' hinfPP' hz2 he2 hze (hswap z hzT hzs) (hswap e heT hes) hV F3
    (fun x hx => F1 L hL hs x (hPL hx)) (fun x hx => F2 L hL hs x (hPL hx))
    (fun x hx => F2 L' hL' hs' x (hP'L' hx))

theorem exists_conj_fusion (hΩ : HypOmegaGen Ω)
    (h8 : ∀ L ∈ Ω, ∀ P : Subgroup G, IsSylow2In P L → Nat.card P = 8) {W S : Subgroup G}
    (hW : W ∈ WSet Ω) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {z e : G} (hzW : z ∈ W)
    (heW : e ∈ W) (he2 : e * e = 1) (hS : IsSylow2In S (Subgroup.centralizer ({z} : Set G)))
    (hWS : W ≤ S) (hSe : S ≤ Subgroup.centralizer ({e} : Set G))
    (hT : ∀ M ∈ Ω, ∀ R : Subgroup G, IsSylow2In R M → R ∈ DSet Ω W → ∀ r : G,
      IsUniqueInvolution M r → ∃ n ∈ Subgroup.centralizer ({e} : Set G), n * z * n⁻¹ = r)
    (hZ : z ∈ zStarOf (Subgroup.centralizer ({e * z} : Set G)))
    (htw : ∀ L ∈ Ω, ∀ s : G, IsUniqueInvolution L s → ∃ L' ∈ Ω, L ≠ L' ∧
      IsUniqueInvolution L' s ∧ ∀ M ∈ Ω, IsUniqueInvolution M s → M = L ∨ M = L')
    {K : Subgroup G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) {x : G}
    (hxG : ∃ g : G, x = g * z * g⁻¹) (hxz : x * z = z * x) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), ∃ y ∈ Subgroup.centralizer ({e} : Set G),
      c * x * c⁻¹ = y * z * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hbad
  push Not at hbad
  obtain ⟨g, rfl⟩ := hxG
  have hL : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  obtain ⟨L', hL', hne, hx', hpair⟩ := htw _ hL _ (hz.conj g)
  set L := conjSub g K with hLdef
  set x := g * z * g⁻¹ with hxdef
  have hx : IsUniqueInvolution L x := hz.conj g
  have hxC : x ∈ (L ⊔ L') ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨Subgroup.mem_sup_left hx.mem, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩
  obtain ⟨Q₀, hQ₀, hxQ₀⟩ := IsSylow2In.exists_ge (isPGroup_zpowers_of_mul_self hx.sq)
    (Subgroup.zpowers_le.mpr hxC)
  have hxQ₀' : x ∈ Q₀ := hxQ₀ (Subgroup.mem_zpowers x)
  obtain ⟨c, hc, hcQ⟩ := CX.exists_conj_le_of_isSylow2In hS hQ₀.2.1 (hQ₀.1.trans inf_le_right)
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hci : c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hc
  have hQ₁ : IsSylow2In (conjSub c⁻¹ Q₀)
      ((conjSub c⁻¹ L ⊔ conjSub c⁻¹ L') ⊓ Subgroup.centralizer ({z} : Set G)) := by
    have := hQ₀.conj c⁻¹
    rwa [conjSub_inf_eq, conjSub_sup_eq, conjSub_eq_self_of_mem hci] at this
  refine false_of_forall_conj_ne hΩ h8 hW hWab hzW heW he2
    hz.sq hS hWS hSe hT hZ
    (hΩ.conjInvariant c⁻¹ L hL) (hΩ.conjInvariant c⁻¹ L' hL')
    (fun h => hne (conjSub_injective c⁻¹ h)) (s := c⁻¹ * x * c)
    (by simpa using hx.conj c⁻¹) (by simpa using hx'.conj c⁻¹) ?_ ?_ hQ₁
    (by simpa using conj_mem_conjSub (n := c⁻¹) hxQ₀') ?_ ?_
  · intro M hM hsM
    have h1 : IsUniqueInvolution (conjSub c M) x := by simpa [mul_assoc] using hsM.conj c
    rcases hpair _ (hΩ.conjInvariant c M hM) h1 with h | h
    · left; rw [← h, conjSub_inv_conjSub]
    · right; rw [← h, conjSub_inv_conjSub]
  · have hczi : c⁻¹ * z = z * c⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcz, mul_inv_cancel_right]
    calc c⁻¹ * x * c * z = c⁻¹ * x * (c * z) := by group
      _ = c⁻¹ * (x * z) * c := by rw [hcz]; group
      _ = c⁻¹ * z * x * c := by rw [hxz]; group
      _ = z * (c⁻¹ * x * c) := by rw [hczi]; group
  · intro w hw
    have h1 : c * w * c⁻¹ ∈ Q₀ := by simpa using mem_conjSub_iff.mp hw
    simpa [mul_assoc] using hcQ _ h1
  · intro c' hc' y hy h
    refine hbad (c' * c⁻¹) (Subgroup.mul_mem _ hc' hci) y hy ?_
    rw [← h]
    group

def swaps4 : List (Equiv.Perm (Fin 4)) :=
  [Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3, Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 2 3]

theorem mem_swaps4 {X : Equiv.Perm (Fin 4)} (hX : X.IsSwap) : X ∈ swaps4 := by
  obtain ⟨x, y, hxy, rfl⟩ := hX
  revert x y
  decide

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
theorem s4_swap_orbit : ∀ a ∈ swaps4, ∀ b ∈ swaps4, ∀ c ∈ swaps4, ∀ d ∈ swaps4, a ≠ b →
    a * b = b * a → c ≠ a → c ≠ b →
      d = a ∨ d = b ∨ c = d ∨ a * c * a⁻¹ = d ∨ b * c * b⁻¹ = d ∨ a * b * c * (a * b)⁻¹ = d := by
  decide

theorem conjSub_cases_of_mem_normalizer (hP : Q3CL.PartIHypG Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hperp : KPerp Ω K = {K, K'}) (hS4 : MuIsoS4 Ω W)
    {RK RK' : Subgroup G} (hRK : IsSylow2In RK K) (hRKD : RK ∈ DSet Ω W)
    (hRK' : IsSylow2In RK' K') (hRK'D : RK' ∈ DSet Ω W) {g : G}
    (hgN : g ∈ Subgroup.normalizer (W : Set G)) (hgK : conjSub g K ≠ K) (hgK' : conjSub g K ≠ K')
    {n : G} (hnN : n ∈ Subgroup.normalizer (W : Set G)) :
    conjSub n K = K ∨ conjSub n K = K' ∨ ∃ m ∈ K ⊔ K', conjSub m (conjSub g K) = conjSub n K := by
  have hΩ := hP.hyp
  obtain ⟨φ, hφ⟩ := L94.exists_swap_equiv hP hW hK htrans hz hK' hne hperp hS4
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨ρ, hρK, hρR⟩ := exists_rep hΩ hW hK hRK hRKD
  obtain ⟨ρ', hρ'K, hρ'R⟩ := exists_rep hΩ hW hK'.1 hRK' hRK'D
  set σ := conjRep hΩ hgN ρ with hσ
  set τ := conjRep hΩ hnN ρ with hτ
  have hσK : σ.K = conjSub g K := by rw [hσ, ← hρK]; rfl
  have hτK : τ.K = conjSub n K := by rw [hτ, ← hρK]; rfl
  have hrK : ρ.r ∈ K := hρK ▸ ρ.hRK.1 ρ.hr
  have hr'K' : ρ'.r ∈ K' := hρ'K ▸ ρ'.hRK.1 ρ'.hr
  set a := T7D.imgQ ρ
  set b := T7D.imgQ ρ'
  set C := T7D.imgQ σ
  set D := T7D.imgQ τ
  have hK'Ω : K' ∈ Ω := hK'.1
  have hz' : IsUniqueInvolution K' z := Asc77.isUniqueInvolution_of_mem_twinSet hz hK'
  have himg : ∀ ρ₁ ρ₂ : Thompson.Rep Ω W, T7D.imgQ ρ₁ = T7D.imgQ ρ₂ → ρ₁.K = ρ₂.K :=
    fun ρ₁ ρ₂ h => c.K_eq_of_img_eq ρ₁ ρ₂ (congrArg Subtype.val h)
  have hab : a ≠ b := fun h => hne (by rw [← hρK, ← hρ'K]; exact (himg ρ ρ' h).symm)
  have hcomm : a * b = b * a := by
    apply Subtype.ext
    show ρ.img * ρ'.img = ρ'.img * ρ.img
    have hnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
      rw [hρK, hρ'K]
      exact Q3CL.T3.twin_mem_omegaNbr hΩ hK hK'Ω hne hz hz'
    exact Q3CL.Thompson.piG_comm_of_mem_omegaNbr Sec6Gen.l6_2Gen hΩ hW c.hkey ρ.hK ρ'.hK
      (by rw [hρK, hρ'K]; exact hne.symm) ρ.hR ρ'.hR ρ.hRK ρ'.hRK hnbr ρ.hr ρ'.hr ρ.hrW
  have hCa : C ≠ a := fun h => hgK (by rw [← hσK, ← hρK]; exact himg σ ρ h)
  have hCb : C ≠ b := fun h => hgK' (by rw [← hσK, ← hρ'K]; exact himg σ ρ' h)
  have hsw : ∀ x : ↥(muGroup Ω W), x ∈ Thompson.muDelta Ω W → φ x ∈ swaps4 :=
    fun x hx => mem_swaps4 ((hφ x).mp hx)
  have key := s4_swap_orbit _ (hsw a (T7D.imgQ_mem ρ)) _ (hsw b (T7D.imgQ_mem ρ')) _
    (hsw C (T7D.imgQ_mem σ)) _ (hsw D (T7D.imgQ_mem τ)) (fun h => hab (φ.injective h))
    (by rw [← map_mul, ← map_mul, hcomm]) (fun h => hCa (φ.injective h))
    (fun h => hCb (φ.injective h))
  simp only [← map_mul, ← map_inv, φ.injective.eq_iff] at key
  have hlift : ∀ m : G, (hm : m ∈ Subgroup.normalizer (W : Set G)) →
      Thompson.piG W m * σ.img * (Thompson.piG W m)⁻¹ = τ.img →
        conjSub m (conjSub g K) = conjSub n K := by
    intro m hm h
    have := c.K_eq_of_img_eq (conjRep hΩ hm σ) τ (by rw [conjRep_img, h])
    rw [← hσK, ← hτK]
    exact this
  have hrN : ρ.r ∈ Subgroup.normalizer (W : Set G) := ρ.r_mem_normalizer
  have hr'N : ρ'.r ∈ Subgroup.normalizer (W : Set G) := ρ'.r_mem_normalizer
  rcases key with h | h | h | h | h | h
  · left; rw [← hτK, ← hρK]; exact himg τ ρ h
  · right; left; rw [← hτK, ← hρ'K]; exact himg τ ρ' h
  · right; right
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [conjSub_one, ← hσK, ← hτK]
    exact himg σ τ h
  · right; right
    refine ⟨ρ.r, Subgroup.mem_sup_left hrK, hlift _ hrN ?_⟩
    exact congrArg Subtype.val h
  · right; right
    refine ⟨ρ'.r, Subgroup.mem_sup_right hr'K', hlift _ hr'N ?_⟩
    exact congrArg Subtype.val h
  · right; right
    refine ⟨ρ.r * ρ'.r, Subgroup.mul_mem _ (Subgroup.mem_sup_left hrK)
      (Subgroup.mem_sup_right hr'K'), hlift _ (Subgroup.mul_mem _ hrN hr'N) ?_⟩
    have h' := congrArg Subtype.val h
    rw [Thompson.piG_mul hrN hr'N]
    exact h'

end CFSG.ClassicalInvolution.Q3.Sec13.L94T

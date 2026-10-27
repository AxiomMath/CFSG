module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Prop110
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Embed
import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

theorem comm_le_of_chief_nilp {M : Type*} [Group M] {T X Y : Subgroup M}
    (hT : Group.IsNilpotent ↥T) (hTn : T.Normal) (hXT : X ≤ T) (hc : IsChiefPair X Y) :
    ⁅X, T⁆ ≤ Y := by
  have hXn := hc.1
  have hYn := hc.2.1
  have hYX : Y < X := hc.2.2.1
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup M, Z = ⁅X, T⁆ ⊔ Y := ⟨_, rfl⟩
  have hZn : Z.Normal := by rw [hZ]; infer_instance
  have hZX : Z ≤ X := by
    rw [hZ]; exact sup_le (Subgroup.commutator_le_left X T) hYX.le
  have hYZ : Y ≤ Z := by rw [hZ]; exact le_sup_right
  have hTY : T ≤ normalizer (Y : Set M) := by
    intro t _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact (nconj_iff hYn t).symm
  rcases hc.2.2.2 Z hZn hYZ hZX with h | h
  · rw [← h, hZ]; exact le_sup_left
  · exfalso
    have hXle : X ≤ ⁅X, T⁆ ⊔ Y := by rw [← hZ, h]
    exact hYX.not_ge (le_of_le_comm_sup hT hXT hTY hXle)

theorem isChiefFactorIn_map {G : Type} [Group G] (H : Subgroup G) {X Y : Subgroup ↥H}
    (hc : IsChiefPair X Y) :
    IsChiefFactorIn H (X.map H.subtype) (Y.map H.subtype) := by
  have hXn := hc.1
  have hYn := hc.2.1
  have hι : Function.Injective H.subtype := Subtype.val_injective
  have hHnorm : ∀ B : Subgroup ↥H, B.Normal → H ≤ normalizer ((B.map H.subtype : Subgroup G) : Set G) := by
    intro B hB
    have := (map_mem_normalizer_iff H.subtype hι (Q := ⊤) (B := B)).mpr (normalizer_top_of_normal hB)
    rwa [Subgroup.map_top, Subgroup.range_subtype] at this
  refine ⟨?_, ?_, fun h hh => hHnorm X hXn hh, fun h hh => hHnorm Y hYn hh, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  · exact (Subgroup.map_lt_map_iff_of_injective hι).mpr hc.2.2.1
  · intro Z hYZ hZX hZn
    have hZn' : (Z.comap H.subtype).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_comap] at hn ⊢
      have hg : (g : G) ∈ H := g.2
      have := (Subgroup.mem_normalizer_iff.mp (hZn _ hg) (n : G)).mp hn
      simpa using this
    have hle : Z ≤ H.subtype.range := fun z hz => by
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp (hZX hz)
      exact ⟨x, rfl⟩
    have hYZ' : Y ≤ Z.comap H.subtype := fun y hy => hYZ (Subgroup.mem_map_of_mem _ hy)
    have hZX' : Z.comap H.subtype ≤ X := by
      intro x hx
      have := hZX hx
      obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp this
      have : x' = x := hι hxx'
      rw [← this]; exact hx'
    rcases hc.2.2.2 _ hZn' hYZ' hZX' with h | h
    · left
      rw [← Subgroup.map_comap_eq_self hle, h]
    · right
      rw [← Subgroup.map_comap_eq_self hle, h]

theorem step53b_of_sl2quot {G : Type} [Group G] {p : ℕ} (H : Subgroup G) {X Y : Subgroup ↥H}
    (hc : IsChiefPair X Y) (g m : ↥H)
    (hS : Sl2Quot p ↥(closure ({g, m * g * m⁻¹} : Set ↥H))
      ((stabSec X Y hc.2.1).subgroupOf (closure ({g, m * g * m⁻¹} : Set ↥H)))) :
    ∃ h ∈ H, ∃ J : Subgroup G, J = Subgroup.closure {(g : G), h * g * h⁻¹} ∧
      J ≤ nclIn H (zpowers (g : G)) ∧
      ∃ N : Subgroup G, N ≤ J ∧ J ⊓ CV H (X.map H.subtype) (Y.map H.subtype) ≤ N ∧
        ∃ _ : (N.subgroupOf J).Normal,
          HasSL2Model (↥J ⧸ N.subgroupOf J)
            (fun q => (∃ n : ℕ, 1 ≤ n ∧ q = p ^ n) ∨ (p = 3 ∧ q = 5)) := by
  have hι : Function.Injective H.subtype := Subtype.val_injective
  set JH : Subgroup ↥H := closure ({g, m * g * m⁻¹} : Set ↥H) with hJH
  refine ⟨(m : G), m.2, JH.map H.subtype, ?_, ?_, ?_⟩
  · rw [hJH, MonoidHom.map_closure, Set.image_pair]
    simp
  ·
    unfold nclIn
    refine Subgroup.map_mono ?_
    rw [hJH, Subgroup.closure_le]
    intro x hx
    have hg0 : g ∈ ((zpowers (g : G)).subgroupOf H : Subgroup ↥H) := by
      rw [Subgroup.mem_subgroupOf]; exact Subgroup.mem_zpowers _
    have hgN : g ∈ Subgroup.normalClosure (((zpowers (g : G)).subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      Subgroup.subset_normalClosure hg0
    rcases hx with rfl | rfl
    · exact hgN
    · have := (Subgroup.normalClosure_normal).conj_mem g hgN m
      simpa using this
  · obtain ⟨N', hN'n, hCN', F, hF, hFin, hcard, ⟨eq⟩⟩ := hS
    set J : Subgroup G := JH.map H.subtype with hJ
    let e : ↥JH ≃* ↥J := Subgroup.equivMapOfInjective JH H.subtype hι
    have : (N'.map e.toMonoidHom).Normal := Subgroup.Normal.map hN'n e.toMonoidHom e.surjective
    set N'' : Subgroup ↥J := N'.map e.toMonoidHom with hN''
    refine ⟨N''.map J.subtype, Subgroup.map_subtype_le N'', ?_, ?_⟩
    ·
      rintro c ⟨hcJ, hcCV⟩
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hcJ
      have hjstab : j ∈ stabSec X Y hc.2.1 := by
        intro x hx
        have h1 := hcCV.2.2.2 ((x : G)) (Subgroup.mem_map_of_mem _ hx)
        obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h1
        have : y = ⁅x, j⁆ := by
          apply hι
          rw [hyeq]
          simp [commutatorElement_def]
        rw [← this]; exact hy
      have hmemC : (⟨j, hj⟩ : ↥JH) ∈ (stabSec X Y hc.2.1).subgroupOf JH := hjstab
      have hmemN' := hCN' hmemC
      refine Subgroup.mem_map.mpr ⟨e ⟨j, hj⟩, Subgroup.mem_map_of_mem _ hmemN', rfl⟩
    · have hsub : (N''.map J.subtype).subgroupOf J = N'' :=
        Subgroup.comap_map_eq_self_of_injective Subtype.val_injective N''
      have hnorm : ((N''.map J.subtype).subgroupOf J).Normal := by rw [hsub]; infer_instance
      refine ⟨hnorm, F, hF, hFin, hcard, ⟨?_⟩⟩
      exact (QuotientGroup.quotientMulEquivOfEq hsub).trans
        (((QuotientGroup.congr N' N'' e rfl).symm).trans
          (eq.trans (specialLinearGroupEquivStatedSL 2 F)))

theorem pCore_le_pPrimeCore_two {Q : Type} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : pCore p Q ≤ pPrimeCore 2 Q := by
  have hn : (pCore p Q).Normal := CFSG.pCore_normal
  obtain ⟨n, hn'⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := Q) (p := p))
  have hcop : Nat.Coprime 2 (Nat.card (pCore p Q)) := by
    rw [hn']
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr
      (Ne.symm hp2))
  exact le_sSup ⟨hn, hcop⟩

theorem pElement_fitting_eq_one {Q : Type} [Group Q] [Finite Q] (hbot : pPrimeCore 2 Q = ⊥)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x : Q} (hx : x ∈ fittingSubgroup Q)
    (hxp : IsPGroup p ↥(zpowers x)) : x = 1 := by
  set F : Subgroup Q := fittingSubgroup Q with hF
  have hZp : IsPGroup p ↥((zpowers x).subgroupOf F) := by
    intro y
    obtain ⟨k, hk⟩ := hxp ⟨(y : Q), y.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨P', hP'⟩ := hZp.exists_le_sylow
  have hle := Sylow.map_le_pCore (fittingSubgroup_normal (G := Q)) fittingSubgroup_nilpotent p P'
  have hxF : (⟨x, hx⟩ : ↥F) ∈ (zpowers x).subgroupOf F := Subgroup.mem_zpowers x
  have hxP : x ∈ P'.map F.subtype := Subgroup.mem_map_of_mem _ (hP' hxF)
  have h1 := pCore_le_pPrimeCore_two (Q := Q) (p := p) hp2 (hle hxP)
  rw [hbot] at h1
  exact Subgroup.mem_bot.mp h1

theorem fitting_le_pCore_two {Q : Type} [Group Q] [Finite Q] (hbot : pPrimeCore 2 Q = ⊥) :
    fittingSubgroup Q ≤ pCore 2 Q := by
  have hF2 : IsPGroup 2 ↥(fittingSubgroup Q) := by
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro r hr hrd
    by_contra hr2
    have hrf : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrd
    have hxp : IsPGroup r ↥(zpowers (x : Q)) := by
      rw [IsPGroup.iff_card]
      refine ⟨1, ?_⟩
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]
    have := pElement_fitting_eq_one hbot (p := r) hr2 x.2 hxp
    have h1 : x = 1 := Subtype.ext this
    rw [h1, orderOf_one] at hx
    exact hr.one_lt.ne hx
  exact le_sSup ⟨inferInstance, hF2⟩

theorem mem_centralizer_singleton_of_comm_eq_one {W : Type} [Group W] {y g : W}
    (h : ⁅y, g⁆ = 1) : y ∈ centralizer ({g} : Set W) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm

theorem fstar_central_trivial {W : Type} [Group W] [Finite W] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {g : W} (hgp : IsPGroup p ↥(zpowers g))
    (hFcent : ∀ y ∈ pCore 2 (W ⧸ pPrimeCore 2 W), ⁅y, (g : W ⧸ pPrimeCore 2 W)⁆ = 1)
    (hEcent : ∀ y ∈ layer (W ⧸ pPrimeCore 2 W), ⁅y, (g : W ⧸ pPrimeCore 2 W)⁆ = 1) :
    g ∈ pPrimeCore 2 W := by
  have hbot : pPrimeCore 2 (W ⧸ pPrimeCore 2 W) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two
  have hgq : IsPGroup p ↥(zpowers (g : W ⧸ pPrimeCore 2 W)) :=
    isPGroup_zpowers_map (QuotientGroup.mk' (pPrimeCore 2 W)) hgp
  have hgen : generalizedFitting (W ⧸ pPrimeCore 2 W) ≤
      centralizer ({(g : W ⧸ pPrimeCore 2 W)} : Set (W ⧸ pPrimeCore 2 W)) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact mem_centralizer_singleton_of_comm_eq_one (hFcent y (fitting_le_pCore_two hbot hy))
    · exact mem_centralizer_singleton_of_comm_eq_one (hEcent y hy)
  have hmem : (g : W ⧸ pPrimeCore 2 W) ∈ centralizer
      ((generalizedFitting (W ⧸ pPrimeCore 2 W) : Subgroup _) : Set (W ⧸ pPrimeCore 2 W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := (Subgroup.mem_centralizer_iff.mp (hgen hy)) _ rfl
    exact this.symm
  have hF := centralizer_generalizedFitting_le_fitting' (W ⧸ pPrimeCore 2 W) hmem
  have h1 := pElement_fitting_eq_one hbot hp2 hF hgq
  exact (QuotientGroup.eq_one_iff g).mp h1

theorem even_card_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := by
    apply Ring.two_ne_zero
    intro hchar
    have h1 := FiniteField.even_card_iff_char_two.mp hchar
    rw [← Nat.card_eq_fintype_card] at h1
    have h2 : Even (Nat.card F) := Nat.even_iff.mpr h1
    exact (Nat.not_even_iff_odd.mpr hodd) h2
  let n : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![-1, 0; 0, -1], by simp [Matrix.det_fin_two]⟩
  have hn2 : n ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    show ((n * n : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show (!![-1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * !![-1, 0; 0, -1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hn1 : n ≠ 1 := by
    intro h
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [n] at this
    apply h2
    have h3 : (-1 : F) + 1 = 1 + 1 := by rw [this]
    simpa [one_add_one_eq_two] using h3.symm
  have hord : orderOf n = 2 := orderOf_eq_prime hn2 hn1
  calc 2 = orderOf n := hord.symm
    _ ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := orderOf_dvd_natCard n

theorem sl2Quot_even {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {J : Type} [Group J] [Finite J]
    {C : Subgroup J} (h : Sl2Quot p J C) : 2 ∣ Nat.card J := by
  obtain ⟨N, hN, -, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hodd : Odd (Nat.card F) := by
    rcases hcard with ⟨n, -, hn⟩ | ⟨-, h5⟩
    · rw [hn]; exact Odd.pow ((Fact.out : p.Prime).odd_of_ne_two hp2)
    · rw [h5]; decide
  have h1 := even_card_sl2 hodd
  have h2 : Nat.card (J ⧸ N) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := Nat.card_congr e.toEquiv
  rw [← h2] at h1
  exact h1.trans (Subgroup.card_quotient_dvd_card N)

end CFSG.GH74.GLS.Stage2.Signalizer.L53

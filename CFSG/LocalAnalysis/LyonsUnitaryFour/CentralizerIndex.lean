module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.CoprimeIndex
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment

public section

namespace CFSG.LyonsUnitaryFour

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] noncomputable def restrictAction {Q : Type*} [Group Q] {K : Type*} [Group K]
    (φ : Q →* MulAut K) (H : Subgroup K) (hH : ∀ g, ∀ x ∈ H, φ g x ∈ H) : Q →* MulAut H where
  toFun g :=
    { toFun := fun x => ⟨φ g x, hH g x x.2⟩
      invFun := fun x => ⟨φ g⁻¹ x, hH g⁻¹ x x.2⟩
      left_inv := fun x => Subtype.ext (by
        change φ g⁻¹ (φ g x) = x
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl)
      right_inv := fun x => Subtype.ext (by
        change φ g (φ g⁻¹ x) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
      map_mul' := fun x y => Subtype.ext (map_mul (φ g) (x : K) (y : K)) }
  map_one' := by
    ext x
    change φ 1 x = x
    rw [map_one]; rfl
  map_mul' g h := by
    ext x
    change φ (g * h) x = φ g (φ h x)
    rw [map_mul]; rfl

omit [Finite G] in
theorem restrictAction_apply {Q : Type*} [Group Q] {K : Type*} [Group K]
    (φ : Q →* MulAut K) (H : Subgroup K) (hH : ∀ g, ∀ x ∈ H, φ g x ∈ H) (g : Q) (x : H) :
    ((restrictAction φ H hH g x : H) : K) = φ g x := rfl

theorem exists_eq_pow_four_of_factorization {r : ℕ} (hr : r ≠ 0)
    (h : ∀ p : ℕ, 4 ∣ r.factorization p) : ∃ q : ℕ, r = q ^ 4 := by
  refine ⟨r.factorization.prod fun p e => p ^ (e / 4), ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hr]
  unfold Finsupp.prod
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul, Nat.div_mul_cancel (h p)]

theorem index_centralFixed_eq_pow_four_of_odd {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    {K : Type} [Group K] [Finite K] (hK : Odd (Nat.card K))
    (φ : (S : Subgroup G) →* MulAut K) :
    ∃ q : ℕ, (centralFixed (S : Subgroup G) φ).index = q ^ 4 := by
  classical
  set F := centralFixed (S : Subgroup G) φ with hFdef
  have hrF : Nat.card F * F.index = Nat.card K := Subgroup.card_mul_index F
  have hr0 : F.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hF0 : Nat.card F ≠ 0 := Nat.card_pos.ne'
  apply exists_eq_pow_four_of_factorization hr0
  intro p
  by_cases hp : p.Prime
  swap
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]; exact dvd_zero 4
  have : Fact p.Prime := ⟨hp⟩
  have hfac : (Nat.card K).factorization p = (Nat.card F).factorization p +
      F.index.factorization p := by
    rw [← hrF, Nat.factorization_mul hF0 hr0, Finsupp.add_apply]
  by_cases hp2 : p = 2
  · subst hp2
    have hK2 : (Nat.card K).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hK)
        (even_iff_two_dvd.mpr h))
    rw [hK2] at hfac
    rw [show F.index.factorization 2 = 0 by omega]
    exact dvd_zero 4
  have hFinv : ∀ g, ∀ x ∈ F, φ g x ∈ F := by
    intro g x hx e he
    have hge : g * e = e * g := (Subgroup.mem_center_iff.mp he g)
    calc φ e (φ g x) = φ (e * g) x := by rw [map_mul]; rfl
      _ = φ (g * e) x := by rw [hge]
      _ = φ g (φ e x) := by rw [map_mul]; rfl
      _ = φ g x := by rw [hx e he]
  set φF := restrictAction φ F hFinv with hφF
  have hcopK : Nat.Coprime 2 (Nat.card K) := Nat.coprime_two_left.mpr hK
  have hF2 : ¬ 2 ∣ Nat.card F := fun h => (Nat.not_even_iff_odd.mpr hK)
    (even_iff_two_dvd.mpr (h.trans (Subgroup.card_subgroup_dvd_card F)))
  obtain ⟨P₀F, hP₀F⟩ := CFSG.LargeEvenClassification.Helpers.coprime_action_invariant_sylow
    (sylowPrime := p) Nat.prime_two hp S.isPGroup' φF hF2
  set P₀ : Subgroup K := (P₀F : Subgroup F).map F.subtype with hP₀
  have hP₀p : IsPGroup p P₀ := P₀F.isPGroup'.map _
  have hP₀F_le : P₀ ≤ F := Subgroup.map_subtype_le _
  let _ : MulDistribMulAction (S : Subgroup G) K := MulDistribMulAction.compHom K φ
  have hsmul : ∀ (g : (S : Subgroup G)) (x : K), g • x = φ g x := fun g x => rfl
  have hP₀inv : ∀ g : (S : Subgroup G), ∀ x ∈ P₀, g • x ∈ P₀ := by
    rintro g _ ⟨y, hy, rfl⟩
    rw [hsmul]
    have := congrArg (fun H : Subgroup F => H) (hP₀F g)
    have hmem : φF g y ∈ (P₀F : Subgroup F) := by
      rw [← hP₀F g]; exact ⟨y, hy, rfl⟩
    exact ⟨φF g y, hmem, rfl⟩
  obtain ⟨P, hP₀P, hPinv⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing 2 p
    Nat.prime_two hp S.isPGroup' hcopK P₀ hP₀p hP₀inv
  have hPF : (P : Subgroup K) ⊓ F = P₀ := by
    apply le_antisymm
    · have hX : IsPGroup p (((P : Subgroup K) ⊓ F).subgroupOf F) :=
        (P.isPGroup'.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      have hle : (P₀F : Subgroup F) ≤ ((P : Subgroup K) ⊓ F).subgroupOf F := by
        intro y hy
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hP₀P ⟨y, hy, rfl⟩, y.2⟩
      have heq := P₀F.is_maximal' hX hle
      intro x hx
      have hx' : (⟨x, hx.2⟩ : F) ∈ ((P : Subgroup K) ⊓ F).subgroupOf F :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [heq] at hx'
      exact ⟨⟨x, hx.2⟩, hx', rfl⟩
    · exact le_inf hP₀P hP₀F_le
  have hPinv' : ∀ g, ∀ x ∈ (P : Subgroup K), φ g x ∈ (P : Subgroup K) := by
    intro g x hx
    have h1 : g • x ∈ g • (P : Subgroup K) := Subgroup.smul_mem_pointwise_smul x g _ hx
    have h2 : g • (P : Subgroup K) = (P : Subgroup K) := by
      have := congrArg (fun Q : Sylow p K => (Q : Subgroup K)) (hPinv g)
      simpa [Sylow.pointwise_smul_def] using this
    rw [h2] at h1
    exact h1
  set φP := restrictAction φ (P : Subgroup K) hPinv' with hφP
  have hfixP : centralFixed (S : Subgroup G) φP = F.subgroupOf (P : Subgroup K) := by
    ext x
    rw [mem_centralFixed, Subgroup.mem_subgroupOf, hFdef, mem_centralFixed]
    constructor
    · intro h e he
      have := congrArg Subtype.val (h e he)
      exact this
    · intro h e he
      exact Subtype.ext (h e he)
  obtain ⟨m, hm, -⟩ := unitary_four_coprime_centralizer_index_fourth_power hT S U hSU hp hp2
    P.isPGroup' φP
  have hcardP := Subgroup.card_mul_index (centralFixed (S : Subgroup G) φP)
  rw [hm, hfixP, card_subgroupOf_eq_card_inf, inf_comm, hPF, hP₀,
    Subgroup.card_map_of_injective F.subtype_injective, P₀F.card_eq_multiplicity,
    P.card_eq_multiplicity, ← pow_add] at hcardP
  have hexp := Nat.pow_right_injective hp.two_le hcardP
  refine ⟨m, ?_⟩
  omega

theorem unitary_four_involution_centralizer_index_fourth_power {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) {z : G}
    (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) (hz1 : z ≠ 1) :
    ∃ q : ℕ, Odd q ∧ (Subgroup.centralizer (((Subgroup.center (S : Subgroup G)).map
      (S : Subgroup G).subtype : Subgroup G) : Set G)).relIndex
        (Subgroup.centralizer ({z} : Set G)) = q ^ 4 := by
  classical
  obtain ⟨-, -, hsq1, -, hZcard⟩ := unitary_four_sylow_structure hT S U hSU
  set Z := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set D := Subgroup.centralizer (Z : Set G) with hD
  set K := CFSG.oddCore C with hK
  obtain ⟨y, hy, rfl⟩ := hzZ
  have hy1 : y ≠ 1 := fun h => hz1 (by rw [h]; rfl)
  have hinv : ∀ t : (S : Subgroup G), orderOf t = 2 → t ∈ Subgroup.center (S : Subgroup G) :=
    fun t ht => (hsq1 t).mp (by have := pow_orderOf_eq_one t; rwa [ht] at this)
  obtain ⟨hDK, -⟩ := central_four_involution_centralizer_oddCore S hZcard
    (fun w hw => (hsq1 w).mpr hw) hinv y hy hy1
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨s, hs⟩))
  set φK : (S : Subgroup G) →* MulAut K :=
    (MulAut.conjNormal : C →* MulAut K).comp (Subgroup.inclusion hSC) with hφK
  have hφKapply : ∀ (s : (S : Subgroup G)) (k : K),
      (((φK s k : K) : C) : G) = (s : G) * ((k : C) : G) * (s : G)⁻¹ := by
    intro s k
    simp [hφK, MulAut.conjNormal_apply]
  obtain ⟨q, hq⟩ := index_centralFixed_eq_pow_four_of_odd hT S U hSU (odd_card_oddCore C) φK
  set D' := D.subgroupOf C with hD'
  have hfix : centralFixed (S : Subgroup G) φK = D'.subgroupOf K := by
    ext k
    rw [mem_centralFixed, Subgroup.mem_subgroupOf, hD', Subgroup.mem_subgroupOf, hD,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h w hw
      obtain ⟨e, he, rfl⟩ := hw
      have h1 := congrArg (fun x : K => ((x : C) : G)) (h e he)
      simp only [hφKapply] at h1
      calc ((S : Subgroup G).subtype e) * ((k : C) : G)
          = ((e : G) * ((k : C) : G) * (e : G)⁻¹) * e := by simp
        _ = ((k : C) : G) * ((S : Subgroup G).subtype e) := by rw [h1]; rfl
    · intro h e he
      apply Subtype.ext; apply Subtype.ext
      rw [hφKapply]
      have h1 := h (e : G) ⟨e, he, rfl⟩
      rw [h1, mul_inv_cancel_right]
  have hDC : D ≤ C := fun d hd => Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hd) (y : G) ⟨y, hy, rfl⟩).symm
  have hsup : D' ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨d, hd, k, ⟨k', hk', rfl⟩, hc⟩ := hDK c c.2
    have hc' : c = ((⟨d, hDC hd⟩ : C) * ⟨k'.1, k'.2⟩ : C) := Subtype.ext (by rw [hc]; try rfl)
    rw [hc']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hd) hk'
  have h1 := Subgroup.card_mul_index D'
  have h2 := Subgroup.card_mul_index (D'.subgroupOf K)
  have h3 := Subgroup.card_mul_index (K.subgroupOf D')
  have h4 := Subgroup.card_mul_index (K.subgroupOf (D' ⊔ K))
  have hrel := Subgroup.relIndex_sup_right D' K
  unfold Subgroup.relIndex at hrel
  rw [card_subgroupOf_eq_card_inf] at h2 h3 h4
  rw [inf_of_le_left le_sup_right, hrel, hsup, Subgroup.card_top] at h4
  rw [inf_comm] at h3
  have hpos : 0 < Nat.card (D' ⊓ K : Subgroup C) := Nat.card_pos
  have htpos : 0 < (K.subgroupOf D').index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hidx : D'.index = (D'.subgroupOf K).index := by
    have e1 : Nat.card (D' ⊓ K : Subgroup C) * (K.subgroupOf D').index * D'.index =
        Nat.card (D' ⊓ K : Subgroup C) * (K.subgroupOf D').index * (D'.subgroupOf K).index := by
      calc Nat.card (D' ⊓ K : Subgroup C) * (K.subgroupOf D').index * D'.index
          = Nat.card D' * D'.index := by rw [h3]
        _ = Nat.card C := h1
        _ = Nat.card K * (K.subgroupOf D').index := h4.symm
        _ = Nat.card (D' ⊓ K : Subgroup C) * (D'.subgroupOf K).index *
            (K.subgroupOf D').index := by rw [h2]
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos htpos) e1
  have hodd : Odd (D'.subgroupOf K).index :=
    Odd.of_dvd_nat (odd_card_oddCore C) (Subgroup.index_dvd_card _)
  rw [← hfix, hq] at hodd
  refine ⟨q, Odd.of_dvd_nat hodd (dvd_pow_self q (by norm_num)), ?_⟩
  change D'.index = q ^ 4
  rw [hidx, ← hfix, hq]

end CFSG.LyonsUnitaryFour

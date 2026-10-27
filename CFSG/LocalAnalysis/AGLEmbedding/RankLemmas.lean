module

public import CFSG.LocalAnalysis.AGLEmbedding.IsolatedVertex
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem finrank_comap_le_finrank_add_finrank_ker {K V W : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (P : Submodule K W) :
    Module.finrank K (P.comap f) ≤ Module.finrank K P + Module.finrank K (LinearMap.ker f) := by
  let f' : P.comap f →ₗ[K] P := f.restrict fun _ hx => hx
  have hk : Module.finrank K (LinearMap.ker f') ≤ Module.finrank K (LinearMap.ker f) := by
    rw [← Submodule.finrank_map_subtype_eq]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val hx
  have hr : Module.finrank K (LinearMap.range f') ≤ Module.finrank K P := Submodule.finrank_le _
  have := f'.finrank_range_add_finrank_ker
  omega

theorem finrank_le_mul_finrank_ker_of_pow_eq_zero {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (N : V →ₗ[K] V) (k : ℕ) (hN : N ^ k = 0) :
    Module.finrank K V ≤ k * Module.finrank K (LinearMap.ker N) := by
  have key : ∀ j : ℕ,
      Module.finrank K (LinearMap.ker (N ^ j)) ≤ j * Module.finrank K (LinearMap.ker N) := by
    intro j
    induction j with
    | zero => simp [Module.End.one_eq_id]
    | succ j ih =>
      rw [pow_succ, Module.End.mul_eq_comp, LinearMap.ker_comp, Nat.succ_mul]
      exact (finrank_comap_le_finrank_add_finrank_ker N _).trans (by omega)
  have := key k
  rwa [hN, LinearMap.ker_zero, finrank_top] at this

omit [Finite G] in
private theorem isPGroup_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite G] in
private theorem isElemAbelian_of_le {E F : Subgroup G} (hF : IsElemAbelian p F) (hEF : E ≤ F) :
    IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hF hEF

open scoped IsMulCommutative in
theorem card_le_card_inf_centralizer_pow (hp : p.Prime) {A : Subgroup G} (hA : IsElemAbelian p A)
    {v : G} (hv : v ∈ Subgroup.normalizer (A : Set G)) (hvp : v ^ p = 1) :
    Nat.card A ≤ Nat.card (A ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) ^ p := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsMulCommutative A := hA.1
  let _ : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule (n := p) fun x =>
    Additive.toMul.injective (Subtype.ext (hA.2 _ (Additive.toMul x).2))
  let c : A →* A :=
    { toFun := fun a => ⟨v * a * v⁻¹, (Subgroup.mem_normalizer_iff.mp hv a).mp a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  let g : Additive A →ₗ[ZMod p] Additive A := (MonoidHom.toAdditive c).toZModLinearMap p
  have hiter : ∀ (n : ℕ) (x : Additive A), ((Additive.toMul (g^[n] x) : A) : G) =
      v ^ n * (Additive.toMul x : A) * (v ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change v * ((Additive.toMul (g^[n] x) : A) : G) * v⁻¹ = _
      rw [ih, pow_succ']
      group
  have hg : g ^ p = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.pow_apply, Module.End.one_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hiter, hvp, one_mul, inv_one, mul_one]
  have hN : (g - 1) ^ p = 0 := by
    have hpoly : ((Polynomial.X - 1 : Polynomial (ZMod p)) ^ p) = Polynomial.X ^ p - 1 := by
      rw [sub_pow_char, one_pow]
    have := congrArg (Polynomial.aeval g) hpoly
    simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at this
    rw [this, hg, sub_self]
  have hfin := finrank_le_mul_finrank_ker_of_pow_eq_zero (g - 1) p hN
  have hcardA : Nat.card A = p ^ Module.finrank (ZMod p) (Additive A) :=
    (FiniteField.pow_finrank_eq_natCard p (Additive A)).symm
  have hcardK : Nat.card (LinearMap.ker (g - 1)) =
      p ^ Module.finrank (ZMod p) (LinearMap.ker (g - 1)) :=
    (FiniteField.pow_finrank_eq_natCard p _).symm
  have hinj : Nat.card (LinearMap.ker (g - 1)) ≤
      Nat.card (A ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((Additive.toMul x.1 : A) : G), (Additive.toMul x.1).2, ?_⟩) ?_
    · have hx := x.2
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
      have h1 := congrArg (fun y => ((Additive.toMul y : A) : G)) hx
      change v * ((Additive.toMul x.1 : A) : G) * v⁻¹ = _ at h1
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ rfl
      exact mul_inv_eq_iff_eq_mul.mp h1
    · intro x y hxy
      have h2 : ((Additive.toMul x.1 : A) : G) = ((Additive.toMul y.1 : A) : G) :=
        congrArg (fun z : (A ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) => (z : G)) hxy
      exact Subtype.ext (Additive.toMul.injective (Subtype.ext h2))
  calc Nat.card A = p ^ Module.finrank (ZMod p) (Additive A) := hcardA
    _ ≤ p ^ (p * Module.finrank (ZMod p) (LinearMap.ker (g - 1))) :=
      Nat.pow_le_pow_right hp.pos hfin
    _ = (p ^ Module.finrank (ZMod p) (LinearMap.ker (g - 1))) ^ p := by rw [mul_comm, pow_mul]
    _ = Nat.card (LinearMap.ker (g - 1)) ^ p := by rw [hcardK]
    _ ≤ _ := Nat.pow_le_pow_left hinj p

theorem three_le_pRank_centralizer_of_normal_elemAbelian (hp : p.Prime) {R A : Subgroup G}
    (hAR : A ≤ R) (hAn : R ≤ Subgroup.normalizer (A : Set G))
    (hA : IsElemAbelian p A) {n : ℕ} (hAcard : Nat.card A = p ^ n) (hn : p + 1 ≤ n)
    {v : G} (hvR : v ∈ R) (hvp : v ^ p = 1) :
    3 ≤ Open.pRank p (R ⊓ Subgroup.centralizer ({v} : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 := hp.two_le
  set C : Subgroup G := A ⊓ Subgroup.centralizer ({v} : Set G) with hC
  have hCA : C ≤ A := inf_le_left
  have hCE : IsElemAbelian p C := isElemAbelian_of_le hA hCA
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hCE)
  have hle := card_le_card_inf_centralizer_pow hp hA (hAn hvR) hvp
  rw [hAcard, ← hC, hd, ← pow_mul] at hle
  have hnd : n ≤ d * p := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hd2 : 2 ≤ d := by
    by_contra hlt
    have : d * p ≤ 1 * p := Nat.mul_le_mul_right p (by omega)
    omega
  by_cases hvA : v ∈ A
  · have : IsMulCommutative A := hA.1
    have hAle : A ≤ R ⊓ Subgroup.centralizer ({v} : Set G) := by
      refine le_inf hAR fun a ha => Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ rfl
      exact setLike_mul_comm hvA ha
    exact (show 3 ≤ n by omega).trans (le_csSup (pRank_bddAbove p hp _) ⟨A, hAle, hA, hAcard⟩)
  · have hvC : v ∈ Subgroup.centralizer (C : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun c hc =>
        ((Subgroup.mem_centralizer_iff.mp hc.2) v rfl).symm
    have hE := isElemAbelian_sup_zpowers_of_mem_centralizer hCE hvC hvp
    have hEle : C ⊔ Subgroup.zpowers v ≤ R ⊓ Subgroup.centralizer ({v} : Set G) :=
      sup_le (inf_le_inf_right _ hAR) (Subgroup.zpowers_le.mpr
        ⟨hvR, Subgroup.mem_centralizer_iff.mpr fun _ h => by rw [Set.mem_singleton_iff.mp h]⟩)
    have hlt : C < C ⊔ Subgroup.zpowers v := lt_of_le_of_ne le_sup_left fun h =>
      hvA (hCA (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers v)))
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE)
    have hcard := Subgroup.card_lt_of_lt hlt
    rw [hd, hm, pow_lt_pow_iff_right₀ hp.one_lt] at hcard
    exact (show 3 ≤ m by omega).trans (le_csSup (pRank_bddAbove p hp _) ⟨_, hEle, hE, hm⟩)

theorem card_le_of_normal_elemAbelian_of_pRank_centralizer_le_two (hp : p.Prime)
    {R A : Subgroup G} (hAR : A ≤ R) (hAn : R ≤ Subgroup.normalizer (A : Set G))
    (hA : IsElemAbelian p A) {v : G} (hvR : v ∈ R) (hvp : v ^ p = 1)
    (hv : Open.pRank p (R ⊓ Subgroup.centralizer ({v} : Set G)) ≤ 2) :
    Nat.card A ≤ p ^ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hA)
  rw [hn]
  refine Nat.pow_le_pow_right hp.pos (not_lt.mp fun hlt => ?_)
  have := three_le_pRank_centralizer_of_normal_elemAbelian hp hAR hAn hA hn hlt hvR hvp
  omega

theorem pRank_le_pRank_inf_ker_add_pRank_map (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    (f : G →* H) (R : Subgroup G) :
    Open.pRank p R ≤ Open.pRank p (R ⊓ f.ker) + Open.pRank p (R.map f) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hER, hE, hEcard⟩ := pRank_attained p hp R
  have hK : IsElemAbelian p (f.ker ⊓ E) := isElemAbelian_of_le hE inf_le_right
  have hM : IsElemAbelian p (E.map f) := elementary_abelian_map p hE f
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hK)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hM)
  have hprod := Subgroup.relIndex_mul_card f.ker E
  rw [Subgroup.relIndex_ker, ha, hb, hEcard, ← pow_add] at hprod
  have hsum := Nat.pow_right_injective hp.two_le hprod
  have ha' : a ≤ Open.pRank p (R ⊓ f.ker) :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, le_inf (inf_le_right.trans hER) inf_le_left, hK, ha⟩
  have hb' : b ≤ Open.pRank p (R.map f) :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, Subgroup.map_mono hER, hM, hb⟩
  omega

theorem pRank_le_pRank_inf_add_pRank_map (hp : p.Prime) (N : Subgroup G) [N.Normal]
    (R : Subgroup G) :
    Open.pRank p R ≤ Open.pRank p (R ⊓ N) + Open.pRank p (R.map (QuotientGroup.mk' N)) := by
  have h := pRank_le_pRank_inf_ker_add_pRank_map hp (QuotientGroup.mk' N) R
  rwa [QuotientGroup.ker_mk'] at h

omit [Finite G] in
theorem ker_conjNormal_eq_centralizer (K : Subgroup G) [K.Normal] :
    (MulAut.conjNormal (H := K)).ker = Subgroup.centralizer (K : Set G) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx k hk
    have h := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro hx
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hx k k.2).symm

theorem pRank_le_pRank_inf_centralizer_add_pRank_map_conjNormal (hp : p.Prime) (K : Subgroup G)
    [K.Normal] (R : Subgroup G) :
    Open.pRank p R ≤ Open.pRank p (R ⊓ Subgroup.centralizer (K : Set G)) +
      Open.pRank p (R.map (MulAut.conjNormal (H := K))) := by
  have h := pRank_le_pRank_inf_ker_add_pRank_map hp (MulAut.conjNormal (H := K)) R
  rwa [ker_conjNormal_eq_centralizer] at h

end CFSG.AGLEmbedding

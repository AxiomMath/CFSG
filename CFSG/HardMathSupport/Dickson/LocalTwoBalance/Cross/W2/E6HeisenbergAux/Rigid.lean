module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.NormalForm
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Core
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Graph
public import CFSG.LieType.Chevalley.E6GraphMonomialToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorusDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley

theorem commute_rootSpan_of_commute_pinnedX {L : Type} [Field L] {S : Set (Fin Tag.E6.rank → ℤ)}
    {z : ModGL Tag.E6 L} (h : ∀ β ∈ S, ∀ c : L, Commute z (pinnedX Tag.E6 L β c)) :
    ∀ u ∈ rootSpan Tag.E6 L S, Commute z u := by
  have hle : rootSpan Tag.E6 L S ≤ Subgroup.centralizer {z} := by
    refine iSup₂_le fun β hβ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (h β hβ c).symm.eq
  intro u hu
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm

section Faithful

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem eq_one_of_centralizes_Γ (S : LangSetup .E6 L p) (hd : S.Descends) (hq4 : 4 ≤ S.D.q)
    {v : ModGL .E6 L} (hv : v ∈ adjointGroup .E6 L)
    (h : ∀ y : S.Γ, Commute v (y : ModGL .E6 L)) : v = 1 := by
  obtain ⟨K, _, _, _, e, hq, he⟩ := hd
  obtain ⟨-, -, hcent, -⟩ :=
    Chevalley_large_finite_root_centralizer_faithfulness_of_four_le Tag.E6 K (hq ▸ hq4) L
      (algebraMap K L)
  have hg0 := S.D.g0_mem
  have h1 : S.D.g0 * v * S.D.g0⁻¹ = 1 := by
    refine hcent _ (mul_mem (mul_mem hg0 hv) (inv_mem hg0)) fun x hx => ?_
    obtain ⟨x', hx', rfl⟩ := hx
    have hy := h (e ⟨x', hx'⟩)
    rw [he] at hy
    have hy' : v * (S.D.g0⁻¹ * baseChangeGL (algebraMap K L) x' * S.D.g0) =
        (S.D.g0⁻¹ * baseChangeGL (algebraMap K L) x' * S.D.g0) * v := hy.eq
    calc S.D.g0 * v * S.D.g0⁻¹ * baseChangeGL (algebraMap K L) x' =
          S.D.g0 * (v * (S.D.g0⁻¹ * baseChangeGL (algebraMap K L) x' * S.D.g0)) * S.D.g0⁻¹ := by
            group
      _ = S.D.g0 * ((S.D.g0⁻¹ * baseChangeGL (algebraMap K L) x' * S.D.g0) * v) * S.D.g0⁻¹ := by
            rw [hy']
      _ = baseChangeGL (algebraMap K L) x' * (S.D.g0 * v * S.D.g0⁻¹) := by group
  have h2 : v = S.D.g0⁻¹ * (S.D.g0 * v * S.D.g0⁻¹) * S.D.g0 := by group
  rw [h2, h1]
  group

theorem commute_of_commute_conj (S : LangSetup .E6 L p) (hfaith : FaithfulAt S)
    {z e : ModGL .E6 L}
    (hz : z ∈ adjointGroup .E6 L ∨ ∃ w ∈ adjointGroup .E6 L, z = w * graphP L)
    (he : e ∈ adjointGroup .E6 L) (δ ex : MulAut S.Γ)
    (hδz : ∀ x : S.Γ, (δ x : ModGL .E6 L) = z * x * z⁻¹)
    (hex : ∀ y : S.Γ, (ex y : ModGL .E6 L) = e * y * e⁻¹) (hc : δ * ex = ex * δ) :
    Commute z e := by
  have hv : z⁻¹ * e⁻¹ * z ∈ adjointGroup .E6 L := by
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact mul_mem (mul_mem (inv_mem hz) (inv_mem he)) hz
    · have h1 : (w * graphP L)⁻¹ * e⁻¹ * (w * graphP L) =
          graphP L * (w⁻¹ * e⁻¹ * w) * (graphP L)⁻¹ := by
        have hPinv : (graphP L)⁻¹ = graphP L := diagramMap_E6_inv
        rw [mul_inv_rev, hPinv]
        group
      rw [h1]
      exact E6GraphLevi.diagramMap_conj_mem_adjointGroup' (mul_mem (mul_mem (inv_mem hw)
        (inv_mem he)) hw)
  have hcentr : ∀ y : S.Γ, Commute (z⁻¹ * e⁻¹ * z * e) (y : ModGL .E6 L) := by
    intro y
    have h1 := congrArg (fun φ : MulAut S.Γ => (φ y : ModGL .E6 L)) hc
    simp only [MulAut.mul_apply] at h1
    rw [hδz, hex] at h1
    rw [hex, hδz] at h1
    show z⁻¹ * e⁻¹ * z * e * (y : ModGL .E6 L) = (y : ModGL .E6 L) * (z⁻¹ * e⁻¹ * z * e)
    calc z⁻¹ * e⁻¹ * z * e * (y : ModGL .E6 L)
        = z⁻¹ * e⁻¹ * (z * (e * (y : ModGL .E6 L) * e⁻¹) * z⁻¹) * (z * e) := by group
      _ = z⁻¹ * e⁻¹ * (e * (z * (y : ModGL .E6 L) * z⁻¹) * e⁻¹) * (z * e) := by rw [h1]
      _ = (y : ModGL .E6 L) * (z⁻¹ * e⁻¹ * z * e) := by group
  have h1 := hfaith _ (mul_mem hv he) hcentr
  show z * e = e * z
  calc z * e = (e * z) * (z⁻¹ * e⁻¹ * z * e) := by group
    _ = e * z := by rw [h1, mul_one]

end Faithful

section Kernel

variable {L : Type} [Field L]

theorem exists_kernelRoot (a : Fin Tag.E6.rank → Lˣ)
    (ha : ∀ i, a i ^ 3 = 1) {w : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizer a)
    (hsh : rootChar a (e6Shift w) ≠ 1) : ∃ β, IsRoot Tag.E6 β ∧ rootChar a β = 1 := by
  obtain ⟨b₃, hK, hw₃, hsh₃⟩ := exists_triData a ha hw hsh
  obtain ⟨t, b', hb', hpair, -, -⟩ := exists_rep b₃ hw₃ hsh₃
  refine ⟨t • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ), IsRoot.smul (isRoot_single _ _) t, ?_⟩
  have h0 : t • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots (triChar b₃) := by
    rw [mem_kernelRoots_triChar]
    refine ⟨IsRoot.smul (isRoot_single _ _) t, ?_⟩
    rw [hpair]
    rcases hb' with rfl | rfl <;> decide
  exact ((hK _).2 h0).2

theorem exists_rootSpan_conj_form [IsAlgClosed L] (a b : Fin Tag.E6.rank → Lˣ)
    (w : WeylGroup Tag.E6) {m : ModGL Tag.E6 L}
    (hm : m ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (rootCharKernel a)) :
    ∃ (u : ModGL Tag.E6 L) (b' : Fin Tag.E6.rank → Lˣ),
      u ∈ rootSpan Tag.E6 L (rootCharKernel a) ∧
      m⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * m =
        u⁻¹ * (rootDiagUnit Tag.E6 b' * canonicalRep (coxeterSystem Tag.E6) L w) * u := by
  have hS : ∀ α ∈ rootCharKernel a, IsRoot Tag.E6 α := fun α hα => hα.1
  have hmem := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup Tag.E6 L)
    (rootSpan Tag.E6 L (rootCharKernel a))
    (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan hS)
  rw [← SetLike.mem_coe, hmem] at hm
  obtain ⟨t, ht, u, hu, rfl⟩ := hm
  have hn := canonicalRep_mem_normalizer (R := L) (τ := Tag.E6) w
  have hnt : canonicalRep (coxeterSystem Tag.E6) L w * t *
      (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ ∈ torusGroup Tag.E6 L :=
    (Subgroup.mem_normalizer_iff.1 hn t).1 ht
  have hnew : t⁻¹ * rootDiagUnit Tag.E6 b * (canonicalRep (coxeterSystem Tag.E6) L w * t *
      (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) ∈ torusGroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem ht) (rootDiagUnit_mem_torusGroup b)) hnt
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hnew
  refine ⟨u, b', hu, ?_⟩
  have e : rootDiagUnit Tag.E6 b' * canonicalRep (coxeterSystem Tag.E6) L w =
      t⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * t := by
    rw [← hb']
    group
  show (t * u)⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * (t * u) = _
  calc (t * u)⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * (t * u)
      = u⁻¹ * (t⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * t) *
        u := by
        group
    _ = _ := by rw [← e]

end Kernel

section Rigid

variable {L : Type} [Field L] [IsAlgClosed L]

theorem rigid_single_gen (hAK : AnyKindCommuteT)
    (hbig : ThreeBigComponents) (S : LangSetup .E6 L 3) (hnf : NormalFormAt S)
    (hfaith : FaithfulAt S) (hq4 : 4 ≤ S.D.q)
    (a b : Fin Tag.E6.rank → Lˣ) (ha : ∀ i, a i ^ 3 = 1) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizer a) (hsh : rootChar a (e6Shift w) ≠ 1)
    (haT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    {u : ModGL Tag.E6 L} (hu : u ∈ rootSpan Tag.E6 L (rootCharKernel a))
    (ŷ : ModGL Tag.E6 L)
    (hŷ : ŷ = u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u)
    (ex ey : MulAut S.Γ)
    (hex : ∀ y : S.Γ, (ex y : ModGL Tag.E6 L) =
      rootDiagUnit Tag.E6 a * y * (rootDiagUnit Tag.E6 a)⁻¹)
    (hey : ∀ y : S.Γ, (ey y : ModGL Tag.E6 L) = ŷ * y * ŷ⁻¹)
    (δ : MulAut S.Γ) (hδ : Nat.Coprime 3 (orderOf δ)) (hδx : δ * ex = ex * δ)
    (hδy : δ * ey = ey * δ)
    (hfix : ∀ x : S.Γ, (x : ModGL Tag.E6 L) ∈
      bigComponentSet S (Subgroup.zpowers (rootDiagUnit Tag.E6 a)) → δ x = x) :
    δ = 1 := by
  classical
  set d := rootDiagUnit Tag.E6 a with hd_def
  have ha1 : d ≠ 1 := by
    intro h1
    apply hsh
    have : a = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    subst this
    simp [rootChar]
  have hd3 : d ^ 3 = 1 := by
    rw [hd_def, rootDiagUnit_pow]
    have : a ^ 3 = 1 := funext fun i => by simpa using ha i
    rw [this, rootDiagUnit_one]
  obtain ⟨β0, hβ0r, hβ0χ⟩ := exists_kernelRoot a ha hw hsh
  have hk0 : β0 ∈ kernelRoots (rootCharHom a) := ⟨hβ0r, hβ0χ⟩
  set X := bigComponentSet S (Subgroup.zpowers d) with hX
  have hXΓ : X ⊆ S.Γ := bigComponentSet_subset_Γ S _
  have hF : ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL .E6 L,
        ¬ ∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x := by
    intro r f j _ hr hqf hj0 hjf z hz
    let i0 : KernelComponent (rootCharHom a) := ⟦⟨β0, hk0⟩⟧
    exact outer_false_of_component_fixed_by_twist S (by decide) haT i0 hr hqf
      (Or.inr (Or.inr (Or.inl rfl))) hj0 hjf z fun x hx =>
        hz x ⟨a, Subgroup.mem_zpowers d, ha1, i0, hbig Tag.E6 L S a haT ha1 i0, hx⟩
  obtain ⟨z, hz, hδz⟩ := hnf X hXΓ hF δ hfix
  have hzX : ∀ x ∈ X, Commute z x := by
    intro x hx
    have hxΓ := hXΓ hx
    have h2 := hδz ⟨x, hxΓ⟩
    rw [hfix ⟨x, hxΓ⟩ hx] at h2
    show z * x = x * z
    calc z * x = (z * x * z⁻¹) * z := by group
      _ = x * z := by rw [← h2]
  have hker : ∀ β, IsRoot Tag.E6 β → rootChar a β = 1 → ∀ c : L,
      Commute z (pinnedX Tag.E6 L β c) := by
    intro β hβ hχ c
    have hk : β ∈ kernelRoots (rootCharHom a) := ⟨hβ, hχ⟩
    let i : KernelComponent (rootCharHom a) := ⟦⟨β, hk⟩⟧
    have hγi : β ∈ componentRoots (rootCharHom a) i := ⟨hk, rfl⟩
    obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S haT i
    have hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
      calc 4 ≤ S.D.q := hq4
        _ = S.D.q ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) hs0
    exact hAK Tag.E6 L 3 S (by decide) a haT hd3 i (by omega) hQ z
      (fun x hx => hzX x ⟨a, Subgroup.mem_zpowers d, ha1, i, hbig Tag.E6 L S a haT ha1 i, hx⟩) _
      (pinnedX_mem_rootSpan hγi c)
  have hdG : d ∈ adjointGroup .E6 L := torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup a)
  have hxz : Commute z d := commute_of_commute_conj S hfaith hz hdG δ ex hδz hex hδx
  have hyG : ŷ ∈ adjointGroup .E6 L := by
    rw [hŷ]
    refine mul_mem (mul_mem (inv_mem (rootSpan_le_adjointGroup L _ hu)) (mul_mem ?_
      (canonicalRep_mem_adjointGroup _ L w))) (rootSpan_le_adjointGroup L _ hu)
    exact torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup b)
  have hyz : Commute z ŷ := commute_of_commute_conj S hfaith hz hyG δ ey hδz hey hδy
  have hzu : Commute z u :=
    commute_rootSpan_of_commute_pinnedX (fun β hβ c => hker β hβ.1 hβ.2 c) u hu
  have hy'' : Commute z (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) := by
    have e : rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w = u * ŷ * u⁻¹ := by
      rw [hŷ]
      group
    rw [e]
    exact (hzu.mul_right hyz).mul_right hzu.inv_right
  rcases hz with hz | ⟨g, hg, rfl⟩
  · have hz3 := core_inner a b ha hw hsh hz hker hy''
    have hδ3 : ∀ n : ℕ, ∀ x : S.Γ, ((δ ^ n) x : ModGL .E6 L) = z ^ n * x * (z ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, hδz, ih, pow_succ']
        group
    have hδ3' : δ ^ 3 = 1 := by
      refine MulEquiv.ext fun x => ?_
      rw [MulAut.one_apply]
      apply Subtype.ext
      rw [hδ3, hz3]
      group
    have hdvd := orderOf_dvd_of_pow_eq_one hδ3'
    have h1 : orderOf δ = 1 := by
      have := Nat.Coprime.eq_one_of_dvd hδ.symm hdvd
      exact this
    exact orderOf_eq_one_iff.1 h1
  · exact (graph_coset_false a b ha hw hsh ⟨g, hg, rfl⟩ hker hxz hy'').elim

end Rigid

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

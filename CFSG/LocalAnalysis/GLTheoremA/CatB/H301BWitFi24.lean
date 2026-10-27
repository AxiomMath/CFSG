module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.AGLEmbedding CFSG.AGLEmbedding.R3

private theorem coverWitness_of_spec {Y : Type} [Group Y] [Finite Y]
    (hZ : Nat.card (Subgroup.center Y) = 3) (D : ModuleSpec (Y ⧸ Subgroup.center Y) 3)
    (hD : D.NoAlt) (hF : D.NoFun) {w : Y ⧸ Subgroup.center Y}
    {A : Matrix (Fin D.n) (Fin D.n) (ZMod 3)} (hw : ActsBy D w A) (hA2 : A * A = 1)
    (hA1 : A ≠ 1) {r : ℕ} (v : Fin r → Fin D.n → ZMod 3) (hv : ∀ i, A.mulVec (v i) = v i)
    (hind : ∀ a : Fin r → ZMod 3, ∑ i, a i • v i = 0 → a = 0) :
    ∃ E T : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (r + 1) ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center Y := QuotientGroup.ker_mk' _
  have hZc : IsCyclic (Subgroup.center Y) := isCyclic_of_prime_card (p := 3) hZ
  have hZp : IsPGroup 3 (Subgroup.center Y) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  set Ebar : Subgroup (Y ⧸ Subgroup.center Y) :=
    D.span ⊓ Subgroup.centralizer ({w} : Set (Y ⧸ Subgroup.center Y)) with hEbar
  let lin : (Fin r → ZMod 3) → (Fin D.n → ZMod 3) := fun a => ∑ i, a i • v i
  have hfix : ∀ a, D.elt (lin a) ∈ Ebar := fun a => by
    refine ⟨D.elt_mem _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := conj_elt D hw (lin a)
    rw [show A.mulVec (lin a) = lin a by
      simp only [lin, Matrix.mulVec_sum, Matrix.mulVec_smul, hv]] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hlin : Function.Injective lin := fun a b hab => sub_eq_zero.1 (hind _ (by
    ext k
    have h := congrFun hab k
    simp only [lin, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at h ⊢
    simp only [sub_mul]
    exact (Finset.sum_sub_distrib (s := Finset.univ) (f := fun x => a x * v x k)
      (g := fun x => b x * v x k)).trans (sub_eq_zero.2 h)))
  have hEbar_card : 3 ^ r ≤ Nat.card Ebar := by
    have := Nat.card_le_card_of_injective (fun a => (⟨D.elt (lin a), hfix a⟩ : Ebar))
      fun a b h => hlin (D.elt_injective (congrArg Subtype.val h))
    rwa [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at this
  have hcomm : ∀ x ∈ Ebar.comap π, ∀ y ∈ Ebar.comap π, x * y = y * x := fun x hx y hy =>
    H1420.WitFi24.commute_of_noAlt_any D π Nat.prime_three hπ hker hD x
      (Subgroup.comap_mono inf_le_left hx) y (Subgroup.comap_mono inf_le_left hy)
  have hcube : ∀ x ∈ Ebar.comap π, x ^ 3 = 1 := fun x hx => by
    obtain ⟨z, hz, hxz⟩ := D.exists_pow_eq_pow_of_noFun π Nat.prime_three (by norm_num) hπ hker
      hZp hZc hF x (Subgroup.comap_mono inf_le_left hx)
    have h3 := pow_card_eq_one' (G := Subgroup.center Y) (x := ⟨z, hz⟩)
    rw [hZ] at h3
    rw [hxz]
    exact congrArg Subtype.val h3
  have hEe : IsElemAbelian 3 (Ebar.comap π) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, hcube⟩
  have hEc : 3 ^ (r + 1) ≤ Nat.card (Ebar.comap π) := by
    have h := H1420.WitFi24.card_comap_center Ebar
    rw [hZ] at h
    calc 3 ^ (r + 1) = 3 * 3 ^ r := by ring
      _ ≤ 3 * Nat.card Ebar := Nat.mul_le_mul_left 3 hEbar_card
      _ = Nat.card (Ebar.comap π) := h.symm
  obtain ⟨E, hEle, hE, hEcard⟩ := H1017.exists_elemAbelian_le_of_le hEe hEc
  have hw2 : 2 ∣ orderOf w := by
    by_contra hodd
    obtain ⟨k, hk⟩ : Odd (orderOf w) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    have hpow := H1420.WitFi24.actsBy_pow D hw (orderOf w + 1)
    rw [pow_succ, pow_orderOf_eq_one, one_mul, hk,
      show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, sq, hA2, one_pow] at hpow
    exact hA1 (H1420.WitFi24.actsBy_unique D hw hpow)
  set u := w ^ (orderOf w / 2) with hu
  have hu2 : orderOf u = 2 := orderOf_pow_orderOf_div (orderOf_pos w).ne' hw2
  have hR : Subgroup.zpowers u ≠ ⊥ := fun h => by
    have : u = 1 := Subgroup.mem_bot.1 (h ▸ Subgroup.mem_zpowers u)
    rw [this, orderOf_one] at hu2
    norm_num at hu2
  have hR2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  obtain ⟨R₂, hR₂, hR₂2, hN⟩ := CFSG.SectionRank.QTK.exists_two_subgroup_normalized hR hR2
  refine ⟨E, R₂, hE, hEcard, hR₂, hR₂2, fun y hy => hN y ?_⟩
  have hyw : π y * w = w * π y :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hEle hy)).2
  have hyu : Commute (π y) u := Commute.pow_right hyw _
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  exact (hyu.zpow_right n).eq.symm

section Cert

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native

private theorem coverWitness_of_modCheckV {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ}
    (Sp : OpsSpec O c d) {sA sB : String} {nregs : ℕ} {prog : List Op} {m : NMod}
    {tops : List Pc} {tidx : List ℕ} {s : ℕ} {orb : List (ℕ × ℕ)} {cf : ℕ → ℕ → ℕ → ℤ}
    {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : modCheckV O sA sB nregs prog 3 m tops tidx s orb cf ci ct = true)
    {Y : Type} [Group Y] [Finite Y] (hZ : Nat.card (Subgroup.center Y) = 3)
    (ψ : (certMonoid c d sA sB)ˣ ≃* Y ⧸ Subgroup.center Y)
    (j : Fin m.acts.length) (k : ℕ) {r : ℕ} (v : Fin r → Fin m.basis.length → ZMod 3)
    (hA2 : (actMatN 3 m.basis.length (m.acts.get j)) ^ k *
      (actMatN 3 m.basis.length (m.acts.get j)) ^ k = 1)
    (hA1 : (actMatN 3 m.basis.length (m.acts.get j)) ^ k ≠ 1)
    (hv : ∀ i, ((actMatN 3 m.basis.length (m.acts.get j)) ^ k).mulVec (v i) = v i)
    (hind : ∀ a : Fin r → ZMod 3, ∑ i, a i • v i = 0 → a = 0) :
    ∃ E T : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (r + 1) ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold modCheckV at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hw⟩, -⟩, -⟩, -⟩, -⟩, hfun⟩, halt⟩ := h
  let C : MCert := ⟨nregs, prog, m.modFactsW 3 tops⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.facts 3, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFactsW 3 tops
    simp only [NMod.modFactsW, List.mem_append]
    exact Or.inl hf
  let DS := NMod.specO Sp hC' m hf hw
  let D' := DS.map ψ.toMonoidHom ψ.injective
  have hA : D'.NoAlt := fun B hB hinv => noAlt_of_altOK halt B hB hinv
  have hF : D'.NoFun := fun v hv' => noFun_of_funOK hfun v hv'
  exact coverWitness_of_spec hZ D' hA hF (H1420.WitFi24.actsBy_pow D' (actsBy_g D' j) k) hA2
    hA1 v hv hind

end Cert

section Fi24

open CFSG.RankThree.Asc83Table CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint


set_option maxRecDepth 100000 in
theorem witFi24Cover_holds : CoverTwoRankAttained .Fi24Prime 6 := by
  intro H _ _ hcat hZ
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  let ψ0 : NativeSporadic.Fi24prime ≃*
      (certMonoid 3 781 NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2)ˣ :=
    MulEquiv.refl _
  have φ : NativeSporadic.Fi24prime ≃* H ⧸ Subgroup.center H := b.trans e.symm
  exact coverWitness_of_modCheckV (CFSG.RankThree.Asc83Table.matOpsSpec 3 781)
    (modCheckV_matOps Certificates.certificate9602) hZ
    (ψ0.symm.trans φ) H1420.WitFi24.j9 9 H1420.WitFi24.fixVec H1420.WitFi24.A9_sq
    H1420.WitFi24.A9_ne_one H1420.WitFi24.A9_fix H1420.WitFi24.fixVec_indep

end Fi24

end CFSG.LocalAnalysis.GLTheoremA.H301B

end

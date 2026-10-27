module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24Rank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9594

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

theorem spec_of_modCheckE {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ}
    (Sp : OpsSpec O c d) {sA sB : String} {nregs : ℕ} {prog : List Op} {p : ℕ} [Fact p.Prime]
    {m : NMod} {tops : List Pc} {gs : List NGrp} {cf : ℕ → ℕ → ℕ → ℤ}
    {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : modCheckE O sA sB nregs prog p m tops gs cf ci ct = true) :
    ∃ D : ModuleSpec (certMonoid c d sA sB)ˣ p, D.n = m.basis.length ∧ D.NoAlt ∧ D.NoFun := by
  unfold modCheckE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hC, hw⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hfun⟩, halt⟩ := h
  let C : MCert := ⟨nregs, prog, m.modFactsE p tops gs⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.facts p, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFactsE p tops gs
    simp only [NMod.modFactsE, List.mem_append]
    exact Or.inl (Or.inl hf)
  exact ⟨NMod.spec Sp hC' m hf hw, rfl, fun B hB hinv => noAlt_of_altOK halt B hB hinv,
    fun v hv' => noFun_of_funOK hfun v hv'⟩

theorem coverRank_of_spec {X : Type} [Group X] (D : ModuleSpec X 3) (hA : D.NoAlt)
    (hF : D.NoFun) {H : Type} [Group H] [Finite H] (ψ : X ≃* H ⧸ Subgroup.center H)
    (hZ : Nat.card (Subgroup.center H) = 3) {r : ℕ} (hr : r ≤ D.n + 1) :
    ∃ F : Subgroup H, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D' := D.map ψ.toMonoidHom ψ.injective
  have hA' : D'.NoAlt := hA
  have hF' : D'.NoFun := hF
  set π := QuotientGroup.mk' (Subgroup.center H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center H := QuotientGroup.ker_mk' _
  have hZc : IsCyclic (Subgroup.center H) := isCyclic_of_prime_card (p := 3) hZ
  have hZp : IsPGroup 3 (Subgroup.center H) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hZ1 : Subgroup.center H ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    norm_num at hZ
  have hcomm := CFSG.LocalAnalysis.GLTheoremA.H1420.WitFi24.commute_of_noAlt_any D' π
    Nat.prime_three hπ hker hA'
  have hcard := D'.pow_succ_le_card_omegaOf π Nat.prime_three (by norm_num) hπ hker hZ1 hZp hZc
    hcomm hF'
  obtain ⟨F, -, hFe, hFc⟩ := exists_elemAbelian_le_of_le (isElemAbelian_omegaOf
    (H := D'.span.comap π) (hH := hcomm) (p := 3)) (r := r)
    ((Nat.pow_le_pow_right (by norm_num) hr).trans hcard)
  exact ⟨F, hFe, hFc⟩

theorem coverRank_of_modCheckE {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ}
    (Sp : OpsSpec O c d) {sA sB : String} {nregs : ℕ} {prog : List Op}
    {m : NMod} {tops : List Pc} {gs : List NGrp} {cf : ℕ → ℕ → ℕ → ℤ}
    {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : modCheckE O sA sB nregs prog 3 m tops gs cf ci ct = true)
    {H : Type} [Group H] [Finite H] (ψ : (certMonoid c d sA sB)ˣ ≃* H ⧸ Subgroup.center H)
    (hZ : Nat.card (Subgroup.center H) = 3) {r : ℕ} (hr : r ≤ m.basis.length + 1) :
    ∃ F : Subgroup H, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hn, hA, hF⟩ := spec_of_modCheckE Sp h
  exact coverRank_of_spec D hA hF ψ hZ (by rw [hn]; exact hr)


set_option maxRecDepth 100000 in
theorem i1017SuzCoverRank_holds : I1017SuzCoverRank := by
  intro H _ _ hcat hZ
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Suz
  let ψ0 : NativeSporadic.Carrier .Suz ≃*
      (certMonoid 3 64 NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2)ˣ := MulEquiv.refl _
  have ψ : (certMonoid 3 64 NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2)ˣ ≃*
      H ⧸ Subgroup.center H := (ψ0.symm.trans b).trans e.symm
  exact coverRank_of_modCheckE (spec3 64) Certificates.certificate9594 ψ hZ (r := 5)
    (by decide)

end CFSG.LocalAnalysis.GLTheoremA.H1017

end

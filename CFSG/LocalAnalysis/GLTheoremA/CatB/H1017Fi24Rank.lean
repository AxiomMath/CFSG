module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432Fi24

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

theorem spec_of_modCheckV {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ}
    (Sp : OpsSpec O c d) {sA sB : String} {nregs : ℕ} {prog : List Op} {p : ℕ} [Fact p.Prime]
    {m : NMod} {tops : List Pc} {tidx : List ℕ} {s : ℕ} {orb : List (ℕ × ℕ)}
    {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : modCheckV O sA sB nregs prog p m tops tidx s orb cf ci ct = true) :
    ∃ D : ModuleSpec (certMonoid c d sA sB)ˣ p, D.n = m.basis.length ∧ D.NoAlt ∧ D.NoFun := by
  unfold modCheckV at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hw⟩, -⟩, -⟩, -⟩, -⟩, hfun⟩, halt⟩ := h
  let C : MCert := ⟨nregs, prog, m.modFactsW p tops⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.facts p, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFactsW p tops
    simp only [NMod.modFactsW, List.mem_append]
    exact Or.inl hf
  exact ⟨NMod.specO Sp hC' m hf hw, rfl, fun B hB hinv => noAlt_of_altOK halt B hB hinv,
    fun v hv' => noFun_of_funOK hfun v hv'⟩

theorem isElemAbelian_span_spec {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (D : ModuleSpec X p) : IsElemAbelian p D.span :=
  ⟨⟨⟨fun a b => Subtype.ext (D.mul_comm_of_mem a.2 b.2)⟩⟩, fun _ hx => D.pow_eq_one_of_mem hx⟩

theorem exists_elemAbelian_le_of_le {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {E : Subgroup X} (hE : IsElemAbelian p E) {r : ℕ} (hr : p ^ r ≤ Nat.card E) :
    ∃ F ≤ E, IsElemAbelian p F ∧ Nat.card F = p ^ r := by
  have hp := (Fact.out : p.Prime)
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hEp
  have hrm : r ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hm ▸ hr)
  exact CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hE (n := r)
    (by rw [hm]; exact pow_dvd_pow p hrm)

private theorem comm_of_elemAbelian_r {X : Type} [Group X] {p : ℕ} {E : Subgroup X}
    (hE : IsElemAbelian p E) {x y : X} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  haveI := hE.1
  have := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  simpa using this

theorem isElemAbelian_map_equiv {X Y : Type} [Group X] [Group Y] {p : ℕ} (φ : X ≃* Y)
    {E : Subgroup X} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map φ.toMonoidHom) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, hx, rfl⟩ := a
    obtain ⟨_, y, hy, rfl⟩ := b
    show φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul, comm_of_elemAbelian_r hE hx hy]
  · rintro _ ⟨x, hx, rfl⟩
    show φ x ^ p = 1
    rw [← map_pow, hE.2 x hx, map_one]

theorem elemRank_of_modCheckV {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ}
    (Sp : OpsSpec O c d) {sA sB : String} {nregs : ℕ} {prog : List Op}
    {m : NMod} {tops : List Pc} {tidx : List ℕ} {s : ℕ} {orb : List (ℕ × ℕ)}
    {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : modCheckV O sA sB nregs prog 3 m tops tidx s orb cf ci ct = true)
    {K : Type} [Group K] [Finite K] (ψ : (certMonoid c d sA sB)ˣ ≃* K) {r : ℕ}
    (hr : r ≤ m.basis.length) : ∃ F : Subgroup K, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hn, -, -⟩ := spec_of_modCheckV Sp h
  have hcard : Nat.card (D.span.map ψ.toMonoidHom) = 3 ^ m.basis.length := by
    rw [Subgroup.card_map_of_injective ψ.injective, D.card_span Nat.prime_three, hn]
  obtain ⟨F, -, hF, hFc⟩ := exists_elemAbelian_le_of_le (isElemAbelian_map_equiv ψ
    (isElemAbelian_span_spec D)) (r := r) (by rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) hr)
  exact ⟨F, hF, hFc⟩

theorem coverRank_of_modCheckV {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ}
    (Sp : OpsSpec O c d) {sA sB : String} {nregs : ℕ} {prog : List Op}
    {m : NMod} {tops : List Pc} {tidx : List ℕ} {s : ℕ} {orb : List (ℕ × ℕ)}
    {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : modCheckV O sA sB nregs prog 3 m tops tidx s orb cf ci ct = true)
    {H : Type} [Group H] [Finite H] (ψ : (certMonoid c d sA sB)ˣ ≃* H ⧸ Subgroup.center H)
    (hZ : Nat.card (Subgroup.center H) = 3) {r : ℕ} (hr : r ≤ m.basis.length + 1) :
    ∃ F : Subgroup H, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hn, hA, hF⟩ := spec_of_modCheckV Sp h
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
  have hn' : D'.n = m.basis.length := hn
  rw [hn'] at hcard
  obtain ⟨F, -, hFe, hFc⟩ := exists_elemAbelian_le_of_le (isElemAbelian_omegaOf
    (H := D'.span.comap π) (hH := hcomm) (p := 3)) (r := r)
    ((Nat.pow_le_pow_right (by norm_num) hr).trans hcard)
  exact ⟨F, hFe, hFc⟩


set_option maxRecDepth 100000 in
theorem i1017FiTwoFourRank_holds : I1017FiTwoFourRank := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi24Prime
  let ψ0 : NativeSporadic.Carrier .Fi24Prime ≃*
      (certMonoid 3 781 NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2)ˣ :=
    MulEquiv.refl _
  have ψ : (certMonoid 3 781 NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2)ˣ ≃* K :=
    (ψ0.symm.trans b).trans e.symm
  exact elemRank_of_modCheckV (CFSG.RankThree.Asc83Table.matOpsSpec 3 781)
    (modCheckV_matOps Certificates.certificate9602) ψ (r := 6)
    (by decide)

set_option maxRecDepth 100000 in
theorem i1017FiTwoFourCoverRank_holds : I1017FiTwoFourCoverRank := by
  intro H _ _ hcat hZ
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi24Prime
  let ψ0 : NativeSporadic.Carrier .Fi24Prime ≃*
      (certMonoid 3 781 NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2)ˣ :=
    MulEquiv.refl _
  have ψ : (certMonoid 3 781 NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2)ˣ ≃*
      H ⧸ Subgroup.center H := (ψ0.symm.trans b).trans e.symm
  exact coverRank_of_modCheckV (CFSG.RankThree.Asc83Table.matOpsSpec 3 781)
    (modCheckV_matOps Certificates.certificate9602) ψ hZ (r := 7)
    (by decide)

end CFSG.LocalAnalysis.GLTheoremA.H1017

end

module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem conj_frob_rootDiag_of_conj_eq {τ : Tag} {L : Type} [Field L]
    {F : ModGL τ L →* ModGL τ L} {g u : ModGL τ L}
    {b : Fin τ.rank → Lˣ} (hu : F u = u) (h : g⁻¹ * u * g = rootDiagUnit τ b) :
    (g⁻¹ * F g) * F (rootDiagUnit τ b) * (g⁻¹ * F g)⁻¹ = rootDiagUnit τ b := by
  have hu' : u = g * rootDiagUnit τ b * g⁻¹ := by rw [← h]; group
  have hF : F g * F (rootDiagUnit τ b) * (F g)⁻¹ = g * rootDiagUnit τ b * g⁻¹ := by
    calc F g * F (rootDiagUnit τ b) * (F g)⁻¹
        = F (g * rootDiagUnit τ b * g⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = F u := by rw [← hu']
      _ = u := hu
      _ = g * rootDiagUnit τ b * g⁻¹ := hu'
  calc (g⁻¹ * F g) * F (rootDiagUnit τ b) * (g⁻¹ * F g)⁻¹
      = g⁻¹ * (F g * F (rootDiagUnit τ b) * (F g)⁻¹) * g := by group
    _ = g⁻¹ * (g * rootDiagUnit τ b * g⁻¹) * g := by rw [hF]
    _ = rootDiagUnit τ b := by group

theorem familyKernel_unit_eq_kernelRoots {τ : Tag} {L : Type} [Field L]
    {b : Fin τ.rank → Lˣ} :
    familyKernel (fun _ : Unit => b) = kernelRoots (rootCharHom b) := by
  rw [kernelRoots_rootCharHom]
  ext α
  simp [familyKernel]

theorem inv_conj_rootDiag_of_mem_familyCentralizer {τ : Tag} {L : Type} [Field L]
    {b : Fin τ.rank → Lˣ}
    {z : ModGL τ L} (hz : z ∈ familyCentralizer τ L (fun _ : Unit => b)) :
    z⁻¹ * rootDiagUnit τ b * z = rootDiagUnit τ b := by
  have hcomm := (mem_familyCentralizer.1 hz).2 ()
  have hdz : rootDiagUnit τ b * z = z * rootDiagUnit τ b := by
    calc rootDiagUnit τ b * z
        = (rootDiagUnit τ b * z * (rootDiagUnit τ b)⁻¹) * rootDiagUnit τ b := by group
      _ = z * rootDiagUnit τ b := by rw [hcomm]
  calc z⁻¹ * rootDiagUnit τ b * z = z⁻¹ * (rootDiagUnit τ b * z) := by group
    _ = z⁻¹ * (z * rootDiagUnit τ b) := by rw [hdz]
    _ = rootDiagUnit τ b := by group

theorem canonicalRep_mem_familyGroup_of_mem_kernelWeyl {τ : Tag} {L : Type} [Field L]
    {b : Fin τ.rank → Lˣ} {v : WeylGroup τ} (hv : v ∈ kernelWeylGroup (rootCharHom b)) :
    canonicalRep (coxeterSystem τ) L v ∈ familyGroup (K := L) (fun _ : Unit => b) := by
  have hS : ∀ α ∈ familyKernel (fun _ : Unit => b), IsRoot τ α ∧
      -α ∈ familyKernel (fun _ : Unit => b) := by
    rintro α ⟨hα, hχ⟩
    have hχ1 : rootChar b α = 1 := hχ ()
    have hneg : rootChar b (-α) = 1 := by
      have h := rootChar_sub b 0 α
      rw [zero_sub, rootChar_zero, one_mul, hχ1, inv_one] at h
      exact h
    exact ⟨hα, IsRoot.neg hα, by simpa [familyKernel] using hneg⟩
  have hv' : v ∈ Subgroup.closure {s | ∃ α ∈ familyKernel (fun _ : Unit => b),
      s = rootReflection α} := by
    refine (Subgroup.closure_le _).2 ?_ hv
    rintro r ⟨w, i, hα, rfl⟩
    have hα' : w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ familyKernel (fun _ : Unit => b) := by
      rw [familyKernel_unit_eq_kernelRoots]
      exact hα
    exact Subgroup.subset_closure ⟨_, hα', (rootReflection_eq_conj rfl).symm⟩
  exact CFSG.RankThree.Classical2.canonicalRep_mem_of_mem_closure (K := L) hS hv'

theorem exists_lang_canonicalRep
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]
    (e : ℕ) (he : 1 ≤ e) {p : ℕ} (hpq : Nat.Coprime p (ℓ ^ e))
    {b : Fin τ.rank → Lˣ} (hb : ∀ i, b i ^ p = 1) {u g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hu : entrywiseFrobGL τ L ℓ e u = u) (hgu : g⁻¹ * u * g = rootDiagUnit τ b) :
    ∃ g' ∈ adjointGroup τ L, ∃ w : WeylGroup τ, g'⁻¹ * u * g' = rootDiagUnit τ b ∧
      g'⁻¹ * entrywiseFrobGL τ L ℓ e g' = canonicalRep (coxeterSystem τ) L w := by
  have hn : (g⁻¹ * entrywiseFrobGL τ L ℓ e g) *
      entrywiseFrobGL τ L ℓ e (rootDiagUnit τ b) *
        (g⁻¹ * entrywiseFrobGL τ L ℓ e g)⁻¹ = rootDiagUnit τ b :=
    conj_frob_rootDiag_of_conj_eq (F := entrywiseFrobGL τ L ℓ e) hu hgu
  obtain ⟨w', z, hz, hzF⟩ := exists_lang_datum_of_plane (τ := τ) (L := L) (ι := Unit)
    (ℓ := ℓ) (e := e) he (p := p) hpq (fun _ : Unit => b) (fun _ i => hb i) (g := g) hg
    (fun _ => hn)
  have hzC := familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => b) hz
  refine ⟨g * z, mul_mem hg (mem_familyCentralizer.1 hzC).1, w', ?_, hzF⟩
  calc (g * z)⁻¹ * u * (g * z) = z⁻¹ * (g⁻¹ * u * g) * z := by group
    _ = z⁻¹ * rootDiagUnit τ b * z := by rw [hgu]
    _ = rootDiagUnit τ b := inv_conj_rootDiag_of_mem_familyCentralizer hzC

theorem exists_lang_canonicalRep_kernelWeyl
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (e : ℕ) (he : 1 ≤ e) {p : ℕ} (hp : Odd p)
    {b : Fin τ.rank → Lˣ} (hb : ∀ i, b i ^ p = 1) {u g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hu : entrywiseFrobGL τ L 2 e u = u) (hgu : g⁻¹ * u * g = rootDiagUnit τ b)
    {w : WeylGroup τ}
    (hgw : g⁻¹ * entrywiseFrobGL τ L 2 e g = canonicalRep (coxeterSystem τ) L w)
    {v : WeylGroup τ} (hv : v ∈ kernelWeylGroup (rootCharHom b)) :
    ∃ g' ∈ adjointGroup τ L, g'⁻¹ * u * g' = rootDiagUnit τ b ∧
      g'⁻¹ * entrywiseFrobGL τ L 2 e g' = canonicalRep (coxeterSystem τ) L (v⁻¹ * w) := by
  have hnd : canonicalRep (coxeterSystem τ) L w * entrywiseFrobGL τ L 2 e (rootDiagUnit τ b) *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootDiagUnit τ b := by
    have h := conj_frob_rootDiag_of_conj_eq (F := entrywiseFrobGL τ L 2 e) hu hgu
    rwa [hgw] at h
  have hwchar : ∀ v : Fin τ.rank → ℤ, rootChar b (w • v) = rootChar b v ^ 2 ^ e := by
    intro v
    have h : rootChar b (w • v) = rootChar (b ^ 2 ^ e) v := by
      refine (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) b (b ^ 2 ^ e) w).1 ?_ v
      simpa only [entrywiseFrobGL_rootDiagUnit_eq_pow] using hnd.symm
    rwa [rootChar_pow'] at h
  have hpq2 : Nat.Coprime p (2 ^ e) := (Nat.coprime_two_right.mpr hp).pow_right e
  have himg : (fun α => w • α) '' familyKernel (fun _ : Unit => b) =
      familyKernel (fun _ : Unit => b) :=
    image_familyKernel_of_pow (ℓ := 2) hpq2 (fun _ : Unit => b) (fun _ i => hb i)
      (fun _ v => hwchar v)
  have hwN : canonicalRep (coxeterSystem τ) L w ∈
      Subgroup.normalizer (familyGroup (K := L) (fun _ : Unit => b) : Set (ModGL τ L)) :=
    canonicalRep_mem_normalizer_of_image himg
  have hnv : canonicalRep (coxeterSystem τ) L v ∈ familyGroup (K := L) (fun _ : Unit => b) :=
    canonicalRep_mem_familyGroup_of_mem_kernelWeyl (b := b) (v := v) hv
  have hQeq : canonicalRep (coxeterSystem τ) L (v⁻¹ * w) =
      (canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w := by
    rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
      ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo]
  have hQN : canonicalRep (coxeterSystem τ) L (v⁻¹ * w) ∈
      Subgroup.normalizer (familyGroup (K := L) (fun _ : Unit => b) : Set (ModGL τ L)) := by
    rw [hQeq]
    exact mul_mem (inv_mem (Subgroup.le_normalizer hnv)) hwN
  have hn : g⁻¹ * entrywiseFrobGL τ L 2 e g =
      canonicalRep (coxeterSystem τ) L v * canonicalRep (coxeterSystem τ) L (v⁻¹ * w) := by
    rw [hgw, hQeq]
    group
  obtain ⟨z, hz, hzF⟩ := exists_mem_lang_conj (entrywiseFrobGL τ L 2 e)
    (M := familyGroup (K := L) (fun _ : Unit => b))
    (Q := canonicalRep (coxeterSystem τ) L (v⁻¹ * w))
    (g := g) (m := canonicalRep (coxeterSystem τ) L v) hnv hn
    (lang_familyGroup 2 (fun _ : Unit => b) e he _ hQN)
  have hzC := familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => b) hz
  refine ⟨g * z, mul_mem hg (mem_familyCentralizer.1 hzC).1, ?_, hzF⟩
  calc (g * z)⁻¹ * u * (g * z) = z⁻¹ * (g⁻¹ * u * g) * z := by group
    _ = z⁻¹ * rootDiagUnit τ b * z := by rw [hgu]
    _ = rootDiagUnit τ b := inv_conj_rootDiag_of_mem_familyCentralizer hzC

end CFSG.HardMathSupport.Timmesfeld.Torality

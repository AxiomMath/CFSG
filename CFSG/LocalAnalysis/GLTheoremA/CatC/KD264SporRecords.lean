module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264RowTools

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem exists_comp_of_record {n p : ℕ} (hp : p.Prime) {P D : Subgroup (Equiv.Perm (Fin n))}
    {x : Equiv.Perm (Fin n)} (hxP : x ∈ P) (hxo : orderOf x = p) (hDP : D ≤ P)
    (hs : IsSimpleGroup ↥D) (hnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) (hpD : p ∣ Nat.card ↥D)
    (hxD : x ∈ Subgroup.centralizer (D : Set (Equiv.Perm (Fin n)))) {N : ℕ}
    (hC : Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) ≤ N)
    (hN : N ≤ 2 * (p * Nat.card ↥D)) :
    ∃ J : Subgroup ↥P, GLAPComponent p (Subgroup.centralizer ({⟨x, hxP⟩} : Set ↥P)) J := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x' : ↥P := ⟨x, hxP⟩
  set L : Subgroup ↥P := D.subgroupOf P with hL
  have eL : ↥L ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDP
  haveI : IsSimpleGroup ↥D := hs
  have hsL : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr eL).2 hs
  have hnabL : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hnab
    refine ⟨eL.symm ⟨g, hg⟩, eL.symm ⟨h, hh⟩, fun he => hgh ?_⟩
    have := congrArg (fun z => ((eL z : ↥D) : Equiv.Perm (Fin n))) he
    simpa using this
  have hcardL : Nat.card ↥L = Nat.card ↥D := Nat.card_congr eL.toEquiv
  have hLC : L ≤ Subgroup.centralizer ({x'} : Set ↥P) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h := Subgroup.mem_centralizer_iff.1 hxD (l : Equiv.Perm (Fin n)) (Subgroup.mem_subgroupOf.1 hl)
    exact h
  have hx1 : x' ≠ 1 := fun h1 => by
    have : x = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at hxo
    exact hp.one_lt.ne' hxo.symm
  have hxp : x' ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, ← hxo]
    exact pow_orderOf_eq_one x)
  have hcardC : Nat.card ↥(Subgroup.centralizer ({x'} : Set ↥P)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) := by
    rw [← CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype' P x',
      Subgroup.card_map_of_injective P.subtype_injective]
  exact exists_glaPComponent_of_index2 hp hx1 hxp hLC hsL hnabL (by rw [hcardL]; exact hpD)
    (by rw [hcardC, hcardL]; exact hC.trans hN)

theorem exists_comp_conj {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (g x : T)
    {J₀ : Subgroup T} (hJ₀ : GLAPComponent p (Subgroup.centralizer ({x} : Set T)) J₀) :
    ∃ J₁ : Subgroup T, GLAPComponent p (Subgroup.centralizer ({g * x * g⁻¹} : Set T)) J₁ := by
  have hmap := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp (MulAut.conj g) hJ₀
  rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton (MulAut.conj g) x] at hmap
  exact ⟨_, hmap⟩

theorem kd264RowData_of_lines {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (S₀ : Sylow p T) (hS₀card : Nat.card (S₀ : Subgroup T) = p ^ 3)
    (hS₀nab : ∃ a ∈ (S₀ : Subgroup T), ∃ b ∈ (S₀ : Subgroup T), a * b ≠ b * a)
    {ι : Type*} (line : ι → T) (hlines : ∀ H : Subgroup T, H ≤ S₀ → Nat.card H = p →
      ∃ j, H = Subgroup.zpowers (line j)) (bad : ι)
    (hgood : ∀ j, Subgroup.zpowers (line j) ≠ Subgroup.zpowers (line bad) →
      ∃ J₀ : Subgroup T, GLAPComponent p (Subgroup.centralizer ({line j} : Set T)) J₀) :
    KD264RowData p T := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro A hA hAmax k hk1 hk2 hAk
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian hA
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T S₀ S
  have hmemS : ∀ a ∈ (S : Subgroup T), g⁻¹ * a * g ∈ (S₀ : Subgroup T) := by
    intro a ha
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rw [← hba, MulAut.smul_def, MulAut.conj_apply]
    simpa [mul_assoc] using hb
  have hScard : Nat.card (S : Subgroup T) = p ^ 3 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S₀, hS₀card]
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  swap
  ·
    exfalso
    have hAcard : Nat.card A = p ^ 3 := le_antisymm
      (hScard ▸ Subgroup.card_le_of_le hAS) hAk
    have hAeq : A = S := Subgroup.eq_of_le_of_card_ge hAS (by rw [hAcard, hScard])
    obtain ⟨a, ha, b, hb, hab⟩ := hS₀nab
    have hga : g * a * g⁻¹ ∈ A := by
      rw [hAeq, ← hg, Sylow.coe_subgroup_smul]
      exact ⟨a, ha, rfl⟩
    have hgb : g * b * g⁻¹ ∈ A := by
      rw [hAeq, ← hg, Sylow.coe_subgroup_smul]
      exact ⟨b, hb, rfl⟩
    have hc := hA.1.is_comm.comm (⟨_, hga⟩ : A) ⟨_, hgb⟩
    have hc' : g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) := congrArg Subtype.val hc
    apply hab
    have := congrArg (fun z => g⁻¹ * z * g) hc'
    simpa [mul_assoc] using this
  ·
    have hAk' : p ^ 2 ≤ Nat.card A := by simpa using hAk
    have hp2le : 2 ≤ p := hp.two_le
    have hA1 : 1 < Nat.card A := lt_of_lt_of_le (Nat.one_lt_pow (by norm_num) hp.one_lt) hAk'
    obtain ⟨a, haA, ha1'⟩ : ∃ a ∈ A, a ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : A = ⊥ := eq_bot_iff.2 fun a ha => Subgroup.mem_bot.2 (h a ha)
      rw [hbot, Subgroup.card_bot] at hA1
      omega
    have hao : orderOf a = p := orderOf_eq_prime (hA.2 a haA) ha1'
    have hzA : Subgroup.zpowers a < A := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.2 haA) fun heq => ?_
      have := congrArg (fun H : Subgroup T => Nat.card H) heq
      simp only [Nat.card_zpowers, hao] at this
      rw [← this] at hAk'
      nlinarith
    obtain ⟨b, hbA, hbz⟩ := SetLike.exists_of_lt hzA
    have hb1 : b ≠ 1 := fun h => hbz (h ▸ Subgroup.one_mem _)
    have hbo : orderOf b = p := orderOf_eq_prime (hA.2 b hbA) hb1
    have hline : ∀ c ∈ A, orderOf c = p → ∃ j, Subgroup.zpowers (g⁻¹ * c * g) =
        Subgroup.zpowers (line j) := by
      intro c hc hco
      refine hlines _ (Subgroup.zpowers_le.2 (hmemS c (hAS hc))) ?_
      rw [Nat.card_zpowers, show g⁻¹ * c * g = MulAut.conj g⁻¹ c by simp [MulAut.conj_apply],
        MulEquiv.orderOf_eq, hco]
    obtain ⟨ja, hja⟩ := hline a haA hao
    obtain ⟨jb, hjb⟩ := hline b hbA hbo
    have hcase : ∀ (c : T) (j : ι), c ∈ A → orderOf c = p →
        Subgroup.zpowers (g⁻¹ * c * g) = Subgroup.zpowers (line j) →
        Subgroup.zpowers (line j) ≠ Subgroup.zpowers (line bad) →
        ∃ F : Subgroup T, F ≤ A ∧ Nat.card F = p ^ 1 ∧
          ∃ J₀ : Subgroup T, GLAPComponent p (Subgroup.centralizer (F : Set T)) J₀ := by
      intro c j hc hco hj hne
      obtain ⟨J₀, hJ₀⟩ := hgood j hne
      have hmem : line j ∈ Subgroup.zpowers (g⁻¹ * c * g) := hj ▸ Subgroup.mem_zpowers _
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
      have hceq : Subgroup.centralizer ({g * line j * g⁻¹} : Set T) =
          Subgroup.centralizer ({c} : Set T) := by
        have h1 : Subgroup.zpowers (g * line j * g⁻¹) = Subgroup.zpowers c := by
          have e1 : Subgroup.zpowers (g * line j * g⁻¹) =
              (Subgroup.zpowers (line j)).map (MulAut.conj g).toMonoidHom := by
            rw [MonoidHom.map_zpowers]; rfl
          rw [e1, ← hj, MonoidHom.map_zpowers]
          congr 1
          simp [MulAut.conj_apply, mul_assoc]
        rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, h1,
          Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      obtain ⟨J₁, hJ₁⟩ := exists_comp_conj hp g (line j) hJ₀
      rw [hceq] at hJ₁
      refine ⟨Subgroup.zpowers c, Subgroup.zpowers_le.2 hc, by rw [Nat.card_zpowers, hco, pow_one],
        J₁, ?_⟩
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hJ₁
    by_cases hja' : Subgroup.zpowers (line ja) = Subgroup.zpowers (line bad)
    · by_cases hjb' : Subgroup.zpowers (line jb) = Subgroup.zpowers (line bad)
      · exfalso
        apply hbz
        have h1 : Subgroup.zpowers (g⁻¹ * a * g) = Subgroup.zpowers (g⁻¹ * b * g) := by
          rw [hja, hjb, hja', hjb']
        have h2 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h1
        rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
        have ea : (MulAut.conj g).toMonoidHom (g⁻¹ * a * g) = a := by
          simp [MulAut.conj_apply, mul_assoc]
        have eb : (MulAut.conj g).toMonoidHom (g⁻¹ * b * g) = b := by
          simp [MulAut.conj_apply, mul_assoc]
        rw [ea, eb] at h2
        rw [h2]
        exact Subgroup.mem_zpowers b
      · exact hcase b jb hbA hbo hjb hjb'
    · exact hcase a ja haA hao hja hja'

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen


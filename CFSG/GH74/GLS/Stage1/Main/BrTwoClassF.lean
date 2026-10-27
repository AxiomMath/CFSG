module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassE
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassS
public import CFSG.Walter.ReeOrder.Ward.Quaternion

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Cycle

theorem exists_cycle_L2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ v₁ v₂ w : IVK.L2 F, v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ * v₂ = v₂ * v₁ ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧
      v₁ ≠ v₂ ∧ w * v₁ * w⁻¹ = v₂ ∧ w * v₂ * w⁻¹ = v₁ * v₂ := by
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro hc
    have he := FiniteField.even_card_of_char_two hc
    have h1 : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
    rw [h1] at he
    have := Nat.odd_iff.1 hodd
    omega
  obtain ⟨v₁, v₂, c, h1, h2, hc, h1', h2', h12, -, hc1, hc2⟩ :=
    CFSG.Walter.Ward.Quaternion.exists_quaternion (F := F) hchar
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* IVK.L2 F := (IVK.L2.equivPSL F).symm
  refine ⟨e v₁, e v₂, e c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h1, map_one]
  · rw [← map_mul, h2, map_one]
  · rw [← map_mul, ← map_mul, hc]
  · intro h
    exact h1' (e.injective (h.trans (map_one e).symm))
  · intro h
    exact h2' (e.injective (h.trans (map_one e).symm))
  · intro h
    exact h12 (e.injective h)
  · rw [← map_mul, ← map_inv, ← map_mul, hc1]
  · rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, hc2]

end Cycle

section AutOrdSection

theorem card_mulAut_le_six' {U : Type*} [Group U] [Finite U] (hc : Nat.card U = 4) :
    Nat.card (MulAut U) ≤ 6 := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hT : Fintype.card {u : U // u ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hc]
  let φ : MulAut U → Equiv.Perm {u : U // u ≠ 1} := fun e =>
    Equiv.subtypeEquiv e.toEquiv (fun u => by simp)
  have hφ : Function.Injective φ := by
    intro e e' hee
    ext u
    by_cases hu : u = 1
    · simp [hu]
    · have := congrArg (fun σ => ((σ ⟨u, hu⟩ : {u : U // u ≠ 1}) : U)) hee
      simpa [φ] using this
  calc Nat.card (MulAut U) ≤ Nat.card (Equiv.Perm {u : U // u ≠ 1}) :=
        Nat.card_le_card_of_injective φ hφ
    _ = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, hT]; rfl

variable {G : Type} [Group G] [Finite G] {z : G}

theorem autOrd_of_cycle {V : Subgroup G} (hV4 : IVK.IsFourSubgroup V) {ω : G}
    (hωC : ω ∈ Cen z) (hωN : ∀ v ∈ V, ω * v * ω⁻¹ ∈ V) (hωne : ∃ v ∈ V, ω * v * ω⁻¹ ≠ v)
    (hω3 : ∀ v ∈ V, ω ^ 3 * v * (ω ^ 3)⁻¹ = v) :
    AutOrd (Cen z) V = 3 ∨ AutOrd (Cen z) V = 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := normalizer (V : Set G) ⊓ Cen z
  have hNle : N ≤ normalizer (V : Set G) := inf_le_left
  let α : ↥N →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hNle)
  have hker : α.ker = (centralizer (V : Set G) ⊓ Cen z).subgroupOf N := by
    ext ⟨g, hg⟩
    have h1 : α ⟨g, hg⟩ = 1 ↔ g ∈ centralizer (V : Set G) := by
      have := Subgroup.normalizerMonoidHom_ker V
      have h2 : (⟨g, hNle hg⟩ : ↥(normalizer (V : Set G))) ∈ V.normalizerMonoidHom.ker ↔
          g ∈ centralizer (V : Set G) := by
        rw [this]; exact Iff.rfl
      rw [← h2]; exact Iff.rfl
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, h1]
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, hg.2⟩, fun h => h.1⟩
  have hcard : Nat.card α.range = AutOrd (Cen z) V := by
    rw [← Subgroup.index_ker, hker]; rfl
  have hωn : ω ∈ normalizer (V : Set G) := by
    have : Finite ↥V := inferInstance
    exact Subgroup.mem_normalizer_fintype fun n hn => hωN n hn
  have hωN' : ω ∈ N := ⟨hωn, hωC⟩
  have happ : ∀ (g : ↥N) (u : ↥V), ((α g u : ↥V) : G) = g * u * (g : G)⁻¹ := fun g u => rfl
  have hω3n : ω ^ 3 ∈ N := N.pow_mem hωN' 3
  have hα3 : (α ⟨ω, hωN'⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨ω, hωN'⟩ : ↥N) ^ 3 = ⟨ω ^ 3, hω3n⟩ := Subtype.ext (by simp)
    rw [this]
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [happ]
    exact hω3 v v.2
  have hα1 : α ⟨ω, hωN'⟩ ≠ 1 := by
    intro h
    obtain ⟨v, hv, hne⟩ := hωne
    apply hne
    have := congrArg (fun σ : MulAut ↥V => ((σ ⟨v, hv⟩ : ↥V) : G)) h
    simpa [happ] using this
  have hord : orderOf (α ⟨ω, hωN'⟩) = 3 := orderOf_eq_prime hα3 hα1
  have h3 : 3 ∣ Nat.card α.range := by
    have := Subgroup.orderOf_dvd_natCard α.range (show α ⟨ω, hωN'⟩ ∈ α.range from ⟨_, rfl⟩)
    rw [hord] at this
    exact this
  have hle : Nat.card α.range ≤ 6 := by
    have : Finite (MulAut ↥V) :=
      Finite.of_injective (fun e : MulAut ↥V => (e : ↥V → ↥V)) DFunLike.coe_injective
    exact (Nat.card_le_card_of_injective (fun x : α.range => (x : MulAut ↥V)) Subtype.val_injective).trans
      (card_mulAut_le_six' hV4.2)
  have hpos : 0 < Nat.card α.range := Nat.card_pos
  rw [← hcard]
  omega

end AutOrdSection

section Assembly

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem swapE_of_pair (hpair : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂)
    (ht2 : t * t = 1) :
    ∃ V : Subgroup G, V ≤ LC z ∧ IVK.IsFourSubgroup V ∧
      (AutOrd (Cen z) V = 3 ∨ AutOrd (Cen z) V = 6) ∧ ∀ v ∈ V, t * v = v * t := by
  classical
  obtain ⟨F, iF, fF, hFq, ⟨φ⟩⟩ := exists_CL_iso hpair hsw ht2
  obtain ⟨ht, -, -⟩ := hsw
  have hodd : Odd (Nat.card F) := by
    rw [hFq]
    exact hpair.odd
  obtain ⟨a₁, a₂, a₃, ha₁, ha₂, hca, ha₁1, ha₂1, ha₁₂, hw₁, hw₂⟩ := exists_cycle_L2 hodd
  let ι : IVK.L2 F × Multiplicative (ZMod 2) →* CentralizerBar z :=
    (CL z t).subtype.comp φ.symm.toMonoidHom
  have hιinj : Function.Injective ι := Subtype.coe_injective.comp φ.symm.injective
  have hιmem : ∀ p, ι p ∈ CL z t := fun p => (φ.symm p).2
  have hιL : ∀ p, ι p ∈ LBar z := fun p => (hιmem p).1
  have hιC : ∀ p, ∀ h ∈ (barOf z (zpowers t) : Subgroup (CentralizerBar z)), h * ι p = ι p * h :=
    fun p h hh => Subgroup.mem_centralizer_iff.1 (hιmem p).2 h hh
  have htb : toBar z ⟨t, ht⟩ ∈ (barOf z (zpowers t) : Subgroup (CentralizerBar z)) :=
    ⟨⟨t, ht⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers t), rfl⟩
  set v₁ : CentralizerBar z := ι (a₁, 1) with hv₁def
  set v₂ : CentralizerBar z := ι (a₂, 1) with hv₂def
  set w : CentralizerBar z := ι (a₃, 1) with hwdef
  have hv₁ : v₁ * v₁ = 1 := by
    rw [hv₁def, ← map_mul]
    have : ((a₁, 1) * (a₁, 1) : IVK.L2 F × Multiplicative (ZMod 2)) = 1 :=
      Prod.ext (by simpa using ha₁) (by simp)
    rw [this, map_one]
  have hv₂ : v₂ * v₂ = 1 := by
    rw [hv₂def, ← map_mul]
    have : ((a₂, 1) * (a₂, 1) : IVK.L2 F × Multiplicative (ZMod 2)) = 1 :=
      Prod.ext (by simpa using ha₂) (by simp)
    rw [this, map_one]
  have hc : v₁ * v₂ = v₂ * v₁ := by
    rw [hv₁def, hv₂def, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simpa using hca) (by simp)
  have h₁ : v₁ ≠ 1 := by
    intro h
    have := hιinj (h.trans (map_one ι).symm)
    exact ha₁1 (Prod.mk.inj this).1
  have h₂ : v₂ ≠ 1 := by
    intro h
    have := hιinj (h.trans (map_one ι).symm)
    exact ha₂1 (Prod.mk.inj this).1
  have h₁₂ : v₁ ≠ v₂ := by
    intro h
    have := hιinj h
    exact ha₁₂ (Prod.mk.inj this).1
  have hww₁ : w * v₁ * w⁻¹ = v₂ := by
    rw [hwdef, hv₁def, hv₂def, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Prod.ext (by simpa using hw₁) (by simp)
  have hww₂ : w * v₂ * w⁻¹ = v₁ * v₂ := by
    rw [hwdef, hv₁def, hv₂def, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simpa using hw₂) (by simp)
  have hτ : (⟨t, ht⟩ : ↥(Cen z)) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
  have hN : Odd (Nat.card (pPrimeCore 2 ↥(Cen z))) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  obtain ⟨V', ω, hea, hcard, hτV, himg, hnorm, hne, h3⟩ :=
    exists_lift_four (N := pPrimeCore 2 ↥(Cen z)) hN hτ (v₁ := v₁) (v₂ := v₂) (w := w) hv₁ hv₂ hc h₁ h₂ h₁₂
      (hιC (a₁, 1) _ htb) (hιC (a₂, 1) _ htb) hww₁ hww₂
  have := hea
  have hfour : IVK.IsFourSubgroup (V'.map (Cen z).subtype) := by
    refine ⟨IsElementaryAbelian.map_subtype, ?_⟩
    rw [Subgroup.card_map_of_injective (Cen z).subtype_injective]
    exact hcard
  have hle : V'.map (Cen z).subtype ≤ LC z := by
    rintro _ ⟨v, hv, rfl⟩
    have hv2 : (v : ↥(Cen z)) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
    have hk : (v : ↥(Cen z)) ^ (2 ^ 1) = 1 := by simpa using hv2
    refine (mem_LC_iff_of_pElt (z := z) v hk).2 ?_
    show (QuotientGroup.mk v : CentralizerBar z) ∈ LBar z
    rcases himg v hv with h | h | h | h
    · rw [h]
      exact (LBar z).one_mem
    · rw [h]
      exact hιL (a₁, 1)
    · rw [h]
      exact hιL (a₂, 1)
    · rw [h]
      exact (LBar z).mul_mem (hιL (a₁, 1)) (hιL (a₂, 1))
  have hωN : ∀ g ∈ V'.map (Cen z).subtype, (ω : G) * g * (ω : G)⁻¹ ∈ V'.map (Cen z).subtype := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ω * v * ω⁻¹, hnorm v hv, by simp⟩
  have hne' : ∃ g ∈ V'.map (Cen z).subtype, (ω : G) * g * (ω : G)⁻¹ ≠ g := by
    obtain ⟨v, hv, hvne⟩ := hne
    refine ⟨(v : G), ⟨v, hv, rfl⟩, fun h => hvne (Subtype.ext ?_)⟩
    simpa using h
  have h3' : ∀ g ∈ V'.map (Cen z).subtype, (ω : G) ^ 3 * g * ((ω : G) ^ 3)⁻¹ = g := by
    rintro _ ⟨v, hv, rfl⟩
    have := congrArg Subtype.val (h3 v hv)
    simpa using this
  refine ⟨V'.map (Cen z).subtype, hle, hfour, autOrd_of_cycle hfour ω.2 hωN hne' h3', ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have := congrArg Subtype.val (hτV v hv)
  simpa using this

end Assembly

end CFSG.GH74.GLS.Stage1.Main

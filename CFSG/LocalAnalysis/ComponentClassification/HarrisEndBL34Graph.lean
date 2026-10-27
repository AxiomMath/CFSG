module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Center
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Comp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Seven
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42
open scoped commutatorElement

namespace EndB

theorem commutatorElement_mul_of_commute {G : Type*} [Group G] {a b x y : G}
    (hax : Commute a x) (hab : Commute a b) (hay : Commute a y) (hbx : Commute b x)
    (hby : Commute b y) : ⁅a * x, b * y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hZ : Commute a (x * (b * y) * x⁻¹) :=
    (hax.mul_right (hab.mul_right hay)).mul_right hax.inv_right
  have hW : Commute b (x * y * x⁻¹ * y⁻¹) :=
    ((hbx.mul_right hby).mul_right hbx.inv_right).mul_right hby.inv_right
  calc a * x * (b * y) * (a * x)⁻¹ * (b * y)⁻¹ =
      a * (x * (b * y) * x⁻¹) * a⁻¹ * (b * y)⁻¹ := by group
    _ = x * (b * y) * x⁻¹ * (b * y)⁻¹ := by rw [hZ.eq, mul_inv_cancel_right]
    _ = b * (x * y * x⁻¹ * y⁻¹) * b⁻¹ := by
        rw [show x * (b * y) = b * (x * y) by rw [← mul_assoc, ← hbx.eq, mul_assoc]]
        group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hW.eq, mul_inv_cancel_right]

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB

namespace LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

@[expose] def preCent (π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S)
    (r : Equiv.Perm (Fin 42)) : Subgroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
  ((centralizer {r}).comap PSL3Four.S.subtype).comap π

omit [Finite X] in
theorem mem_preCent {r : Equiv.Perm (Fin 42)}
    {e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))} :
    e ∈ preCent π r ↔ ((π e : PSL3Four.S) : Equiv.Perm (Fin 42)) ∈ centralizer {r} := Iff.rfl

@[expose] def graphCompE
    (π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S)
    (r : Equiv.Perm (Fin 42)) : Subgroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
  ⁅preCent π r, preCent π r⁆

theorem exists_center_mul (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    {e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))}
    (he : e ∈ preCent π (hL.rho g)) :
    ∃ c ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))),
      g * (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹ = (c * e : ↥(layer _)) := by
  set e' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    ⟨g * e * g⁻¹, (inferInstance : (layer (MBar (w ^ (orderOf w / 2) * t ^ i *
      z ^ j))).Normal).conj_mem _ e.2 _⟩ with he'
  have h1 := hL.rho_conj g e e' rfl
  have hc := mem_centralizer_singleton_iff.mp ((mem_preCent).mp he)
  have h2 : π e' = π e := by
    apply Subtype.ext
    rw [← h1, ← hc, mul_inv_cancel_right]
  refine ⟨e' * e⁻¹, ?_, ?_⟩
  · rw [← hL.ker, MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  · rw [inv_mul_cancel_right]

theorem graphComp_le (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    (graphCompE π (hL.rho g)).map (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype ≤
      centralizer {g} := by
  rw [Subgroup.map_le_iff_le_comap, graphCompE, commutator_le]
  intro e₁ he₁ e₂ he₂
  obtain ⟨c₁, hc₁, h₁⟩ := hL.exists_center_mul g he₁
  obtain ⟨c₂, hc₂, h₂⟩ := hL.exists_center_mul g he₂
  rw [mem_comap, Subgroup.coe_subtype, mem_centralizer_singleton_iff]
  have hcomm : ∀ c ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))),
      ∀ e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))), Commute c e :=
    fun c hc e => (mem_center_iff.mp hc e).symm
  have key : g * ((⁅e₁, e₂⁆ : ↥(layer _)) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹ =
      (⁅e₁, e₂⁆ : ↥(layer _)) := by
    have e1 : g * ((⁅e₁, e₂⁆ : ↥(layer _)) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹ =
        ⁅g * (e₁ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹,
          g * (e₂ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1, h₁, h₂]
    have := congrArg Subtype.val (commutatorElement_mul_of_commute (hcomm c₁ hc₁ e₁)
      (hcomm c₁ hc₁ c₂) (hcomm c₁ hc₁ e₂) (hcomm c₂ hc₂ e₁) (hcomm c₂ hc₂ e₂))
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using this
  calc ((⁅e₁, e₂⁆ : ↥(layer _)) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g =
      (g * ((⁅e₁, e₂⁆ : ↥(layer _)) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹) * g := by
        rw [key]
    _ = g * (⁅e₁, e₂⁆ : ↥(layer _)) := by group

theorem graphComp_normal (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    ∀ h ∈ centralizer {g}, ∀ a ∈ (graphCompE π (hL.rho g)).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype,
      h * a * h⁻¹ ∈ (graphCompE π (hL.rho g)).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype := by
  rw [graphCompE, Subgroup.map_commutator]
  refine conj_mem_commutator' (fun h hh x hx => ?_) (fun h hh x hx => ?_) <;>
  · obtain ⟨e, he, rfl⟩ := hx
    set e' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
      ⟨h * e * h⁻¹, (inferInstance : (layer (MBar (w ^ (orderOf w / 2) * t ^ i *
        z ^ j))).Normal).conj_mem _ e.2 _⟩ with he'
    refine ⟨e', ?_, rfl⟩
    rw [SetLike.mem_coe, mem_preCent, mem_centralizer_singleton_iff, ← hL.rho_conj h e e' rfl]
    have hhg : hL.rho h * hL.rho g = hL.rho g * hL.rho h := by
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hh]
    have hhg' : (hL.rho h : Equiv.Perm (Fin 42)) * hL.rho g = hL.rho g * hL.rho h :=
      congrArg Subtype.val hhg
    have hc := mem_centralizer_singleton_iff.mp ((mem_preCent).mp he)
    calc (hL.rho h : Equiv.Perm (Fin 42)) * (π e : Equiv.Perm (Fin 42)) *
          (hL.rho h : Equiv.Perm (Fin 42))⁻¹ * (hL.rho g : Equiv.Perm (Fin 42)) =
        (hL.rho h : Equiv.Perm (Fin 42)) * (π e : Equiv.Perm (Fin 42)) *
          ((hL.rho h : Equiv.Perm (Fin 42))⁻¹ * (hL.rho g : Equiv.Perm (Fin 42)) *
            (hL.rho h : Equiv.Perm (Fin 42))) * (hL.rho h : Equiv.Perm (Fin 42))⁻¹ := by group
      _ = (hL.rho h : Equiv.Perm (Fin 42)) * ((π e : Equiv.Perm (Fin 42)) *
          (hL.rho g : Equiv.Perm (Fin 42))) * (hL.rho h : Equiv.Perm (Fin 42))⁻¹ := by
        rw [show (hL.rho h : Equiv.Perm (Fin 42))⁻¹ * (hL.rho g : Equiv.Perm (Fin 42)) *
          (hL.rho h : Equiv.Perm (Fin 42)) = hL.rho g by rw [mul_assoc, ← hhg']; group]
        group
      _ = (hL.rho g : Equiv.Perm (Fin 42)) * ((hL.rho h : Equiv.Perm (Fin 42)) *
          (π e : Equiv.Perm (Fin 42)) * (hL.rho h : Equiv.Perm (Fin 42))⁻¹) := by
        rw [hc]
        calc (hL.rho h : Equiv.Perm (Fin 42)) * ((hL.rho g : Equiv.Perm (Fin 42)) *
              (π e : Equiv.Perm (Fin 42))) * (hL.rho h : Equiv.Perm (Fin 42))⁻¹ =
            ((hL.rho h : Equiv.Perm (Fin 42)) * (hL.rho g : Equiv.Perm (Fin 42))) *
              (π e : Equiv.Perm (Fin 42)) * (hL.rho h : Equiv.Perm (Fin 42))⁻¹ := by group
          _ = _ := by rw [hhg']; group

theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.isPerfect_of_simple {G : Type*}
    [Group G] [IsSimpleGroup G] (h : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hc | hc
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hmem : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hc, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      at hmem
    exact hab hmem
  · exact hc

theorem graphComp_facts (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hg : ∃ c ∈ PSL3Four.R, ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) =
      c * PSL3Four.r₃ * c⁻¹) :
    IsTwoQuasisimple ↥((graphCompE π (hL.rho g)).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype) ∧
      2 ∣ Nat.card ↥((graphCompE π (hL.rho g)).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype) ∧
      ¬ 7 ∣ Nat.card ↥((graphCompE π (hL.rho g)).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hrc⟩ := hg
  generalize hr : ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) = r at hrc ⊢
  set Cs : Subgroup ↥PSL3Four.S := (centralizer {r}).comap PSL3Four.S.subtype with hCs
  obtain ⟨ψ₃⟩ := nonempty_centralizer_conj_equiv hc hrc
  have hCsmap : Cs.map PSL3Four.S.subtype = centralizer {r} ⊓ PSL3Four.S := by
    rw [hCs, Subgroup.map_comap_eq, range_subtype, inf_comm]
  have eCs : ↥Cs ≃* ↥PSL3Four.C₃ :=
    ((Cs.equivMapOfInjective _ (subtype_injective _)).trans
      (MulEquiv.subgroupCongr hCsmap)).trans ψ₃
  have : IsSimpleGroup PSL3Four.C₃ := PSL3Four.isSimpleGroup_C₃
  have hCsS : IsSimpleGroup ↥Cs := eCs.isSimpleGroup
  have hCsnab : ∃ a b : ↥Cs, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := PSL3Four.exists_mul_ne_C₃
    exact ⟨eCs.symm a, eCs.symm b, fun h => hab (by simpa using congrArg eCs h)⟩
  have hCs60 : Nat.card ↥Cs = 60 := by
    rw [Nat.card_congr eCs.toEquiv]
    exact PSL3Four.card_C₃
  have hCsperf : ⁅Cs, Cs⁆ = Cs :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_simple hCsnab)
  have hC'map : (preCent π r).map π = Cs := map_comap_eq_self_of_surjective hL.surj _
  have hA'map : (graphCompE π r).map π = Cs := by
    rw [graphCompE, Subgroup.map_commutator, hC'map, hCsperf]
  have hdec : ∀ x ∈ preCent π r, ∃ a ∈ graphCompE π r,
      a⁻¹ * x ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    intro x hx
    have hxm : π x ∈ (graphCompE π r).map π := by
      rw [hA'map, ← hC'map]
      exact mem_map_of_mem π hx
    obtain ⟨a, ha, hax⟩ := hxm
    refine ⟨a, ha, ?_⟩
    rw [← hL.ker, MonoidHom.mem_ker, map_mul, map_inv, hax, inv_mul_cancel]
  have hcomm : ∀ c ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))),
      ∀ e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))), Commute c e :=
    fun c hc e => (mem_center_iff.mp hc e).symm
  have hAperf : ⁅graphCompE π r, graphCompE π r⁆ = graphCompE π r := by
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    conv_lhs => rw [graphCompE]
    rw [commutator_le]
    intro x₁ hx₁ x₂ hx₂
    obtain ⟨a₁, ha₁, hz₁⟩ := hdec x₁ hx₁
    obtain ⟨a₂, ha₂, hz₂⟩ := hdec x₂ hx₂
    have e₁ : x₁ = (a₁⁻¹ * x₁) * a₁ := by
      rw [(hcomm _ hz₁ a₁).eq]; group
    have e₂ : x₂ = (a₂⁻¹ * x₂) * a₂ := by
      rw [(hcomm _ hz₂ a₂).eq]; group
    rw [e₁, e₂, commutatorElement_mul_of_commute (hcomm _ hz₁ a₁) (hcomm _ hz₁ _)
      (hcomm _ hz₁ a₂) (hcomm _ hz₂ a₁) (hcomm _ hz₂ a₂)]
    exact commutator_mem_commutator ha₁ ha₂
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥(graphCompE π r) →* ↥PSL3Four.S,
      ψ = π.comp (graphCompE π r).subtype := ⟨_, rfl⟩
  have hψa : ∀ a, ψ a = π a := fun a => by rw [hψ]; rfl
  have hrange : ψ.range = Cs := by
    rw [hψ, MonoidHom.range_comp, range_subtype, hA'map]
  have hkerZ : ∀ a ∈ ψ.ker, ((a : ↥(graphCompE π r)) : ↥(layer (MBar (w ^ (orderOf w / 2) *
      t ^ i * z ^ j)))) ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    intro a ha
    rw [← hL.ker, MonoidHom.mem_ker, ← hψa]
    exact ha
  have hker2 : IsPGroup 2 ↥ψ.ker := by
    refine (hL.isPGroup_center).of_injective (((graphCompE π r).subtype.comp
      ψ.ker.subtype).codRestrict _ fun a => hkerZ a a.2) fun a b h => ?_
    have h1 := congrArg (fun x : ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i *
      z ^ j)))) => (x : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))) h
    exact Subtype.ext (Subtype.ext h1)
  have hZCs : center ↥Cs = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥Cs) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hCsnab
      exact hab ((mem_center_iff.mp (h ▸ mem_top a) b).symm)
  have hcenter : center ↥(graphCompE π r) = ψ.ker := by
    ext a
    constructor
    · intro ha
      have hmem : ∀ b : ↥(graphCompE π r), ψ b ∈ Cs := fun b => by
        rw [← hrange]; exact ⟨b, rfl⟩
      have key : ∀ y ∈ Cs, y * ψ a = ψ a * y := by
        intro y hy
        have hy' : y ∈ ψ.range := by rw [hrange]; exact hy
        obtain ⟨b, hb⟩ := hy'
        have hab := mem_center_iff.mp ha b
        calc y * ψ a = ψ b * ψ a := by rw [hb]
          _ = ψ (b * a) := (map_mul ψ b a).symm
          _ = ψ (a * b) := by rw [hab]
          _ = ψ a * ψ b := map_mul ψ a b
          _ = ψ a * y := by rw [hb]
      have h2 : (⟨ψ a, hmem a⟩ : ↥Cs) ∈ center ↥Cs :=
        mem_center_iff.mpr fun y => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          exact key y y.2)
      rw [hZCs, mem_bot] at h2
      exact congrArg Subtype.val h2
    · intro ha
      rw [mem_center_iff]
      intro b
      apply Subtype.ext
      exact (hcomm _ (hkerZ a ha) b).eq.symm
  let eQ : ↥(graphCompE π r) ⧸ center ↥(graphCompE π r) ≃* ↥Cs :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))
  have hq : IsQuasisimple ↥(graphCompE π r) := by
    refine ⟨Subgroup.isPerfect_iff.mpr hAperf, eQ.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hCsnab
    exact ⟨eQ.symm a, eQ.symm b, fun h => hab (by simpa using congrArg eQ h)⟩
  obtain ⟨k, hk⟩ := hker2.exists_card_eq
  have hcard : Nat.card ↥(graphCompE π r) = 2 ^ k * 60 := by
    rw [← Subgroup.card_ker_mul_card_range ψ, hk, hrange, hCs60]
  have hO : pPrimeCore 2 ↥(graphCompE π r) = ⊥ := by
    rcases LocalCores.quasisimple_normal_subgroups hq
      (inferInstance : (pPrimeCore 2 ↥(graphCompE π r)).Normal) with h | h
    · exfalso
      have hc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(graphCompE π r))) :=
        pPrimeCore_coprime_card
      rw [h, card_top, hcard] at hc
      exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_refl 2)
        (dvd_mul_of_dvd_right (by norm_num : 2 ∣ 60) _) hc
    · rw [hcenter] at h
      have h2 : IsPGroup 2 ↥(pPrimeCore 2 ↥(graphCompE π r)) := hker2.to_le h
      obtain ⟨m, hm⟩ := h2.exists_card_eq
      have hc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(graphCompE π r))) :=
        pPrimeCore_coprime_card
      rw [hm] at hc
      have hm0 : m = 0 := by
        by_contra hm0
        exact absurd hc (by
          rw [Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hm0)]
          norm_num)
      rw [← Subgroup.card_eq_one, hm, hm0, pow_zero]
  have hq2 : IsTwoQuasisimple ↥(graphCompE π r) :=
    ⟨hq.1, LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hq⟩
  have hcardA : Nat.card ↥((graphCompE π r).map
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype) = 2 ^ k * 60 := by
    rw [Subgroup.card_map_of_injective (subtype_injective _), hcard]
  refine ⟨isTwoQuasisimple_of_mulEquiv ((graphCompE π r).equivMapOfInjective _
    (subtype_injective _)) hq2, ?_, ?_⟩
  · rw [hcardA]
    exact dvd_mul_of_dvd_right (by norm_num : 2 ∣ 60) _
  · rw [hcardA]
    intro h7
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)
      omega
    · omega

theorem false_of_graph_conj (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) {g : X}
    (hτM : g * t * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (hr3 : ∃ c ∈ PSL3Four.R, ((hL.rho (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩) : PSL3Four.R) :
      Equiv.Perm (Fin 42)) = c * PSL3Four.r₃ * c⁻¹) : False := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hy2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
    group
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hβC : β ∈ centralizer ({g * t * g⁻¹} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hτM).symm
  have hβne : β ≠ g * t * g⁻¹ := fun h => hs.beta.not_conj g h.symm
  have h44 := hs.lemma44_conj hFC hKC hI hKF g hβC hβ2 hs.beta.ne_one hβne
  obtain ⟨-, hp7, hf1, -⟩ := hL.seven hZ
  rw [hp7, hf1] at h44
  obtain ⟨hq, hA2, hA7⟩ := hL.graphComp_facts _ hr3
  exact false_of_component hτM hy2 h44 (hL.graphComp_le _) (hL.graphComp_normal _) hq hA2 hA7

end LLayer

end EndB

end CFSG.ComponentClassification.HarrisLit

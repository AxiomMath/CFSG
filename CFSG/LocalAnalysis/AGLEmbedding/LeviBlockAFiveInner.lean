module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveGeneric
import CFSG.LargeExtraspecial.S5Comp
import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas

public section

namespace CFSG.AGLEmbedding

open CFSG.Open Subgroup
open scoped commutatorElement

namespace LeviFive

theorem conj_eq_of_conj_mem_center {X : Type*} [Group X] {C : Subgroup X}
    (hC : commutator ↥C = ⊤) {z : X}
    (hz : ∀ u ∈ C, ∃ c ∈ C, (∀ v ∈ C, c * v = v * c) ∧ z * u * z⁻¹ = c * u) :
    ∀ u ∈ C, z * u * z⁻¹ = u := by
  have hle : commutator ↥C ≤ (Subgroup.centralizer ({z} : Set X)).subgroupOf C := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    rintro ⟨a, ha⟩ - ⟨b, hb⟩ -
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨ca, hca, hca', h1⟩ := hz a ha
    obtain ⟨cb, hcb, hcb', h2⟩ := hz b hb
    have e1 : ca * (a * cb * b * a⁻¹) = (a * cb * b * a⁻¹) * ca :=
      hca' _ (C.mul_mem (C.mul_mem (C.mul_mem ha hcb) hb) (C.inv_mem ha))
    have e2 : cb * (b * a⁻¹ * b⁻¹) = (b * a⁻¹ * b⁻¹) * cb :=
      hcb' _ (C.mul_mem (C.mul_mem hb (C.inv_mem ha)) (C.inv_mem hb))
    change a * b * a⁻¹ * b⁻¹ * z = z * (a * b * a⁻¹ * b⁻¹)
    symm
    calc z * (a * b * a⁻¹ * b⁻¹)
        = (z * a * z⁻¹) * (z * b * z⁻¹) * (z * a * z⁻¹)⁻¹ * (z * b * z⁻¹)⁻¹ * z := by group
      _ = (ca * a) * (cb * b) * (ca * a)⁻¹ * (cb * b)⁻¹ * z := by rw [h1, h2]
      _ = ca * (a * cb * b * a⁻¹) * ca⁻¹ * b⁻¹ * cb⁻¹ * z := by group
      _ = a * cb * b * a⁻¹ * b⁻¹ * cb⁻¹ * z := by rw [e1]; group
      _ = a * (cb * (b * a⁻¹ * b⁻¹)) * cb⁻¹ * z := by group
      _ = a * b * a⁻¹ * b⁻¹ * z := by rw [e2]; group
  intro u hu
  have hmem : (⟨u, hu⟩ : ↥C) ∈ (Subgroup.centralizer ({z} : Set X)).subgroupOf C :=
    hle (hC ▸ Subgroup.mem_top _)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hmem
  change u * z = z * u at hmem
  rw [← hmem, mul_inv_cancel_right]

theorem normal_and_inner_of_map {X H : Type*} [Group X] [Finite X] [Group H] {C : Subgroup X}
    (hC : IsComponentOf C ⊤) (Ψ : X →* H) (hM : ∃ a ∈ C, ∃ b ∈ C, Ψ a * Ψ b ≠ Ψ b * Ψ a)
    (hrange : ∀ x, ∃ c ∈ C, Ψ x = Ψ c) :
    C.Normal ∧ ∀ x, ∃ c ∈ C, ∀ u ∈ C, x * u * x⁻¹ = c * u * c⁻¹ := by
  obtain ⟨a, ha, b, hb, hab⟩ := hM
  have hnorm : ∀ x : X, C.map (MulAut.conj x).toMonoidHom = C := by
    intro x
    by_contra hne
    have hC' := CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hC (Subgroup.mem_top x)
    have hcomm := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hC hC' (Ne.symm hne)
    obtain ⟨c, hc, hxc⟩ := hrange x
    have hmem : x * (c⁻¹ * b * c) * x⁻¹ ∈ C.map (MulAut.conj x).toMonoidHom :=
      ⟨c⁻¹ * b * c, C.mul_mem (C.mul_mem (C.inv_mem hc) hb) hc, rfl⟩
    have hΨ : Ψ (x * (c⁻¹ * b * c) * x⁻¹) = Ψ b := by
      simp only [map_mul, map_inv, hxc]
      group
    have h1 := Subgroup.commutator_mem_commutator ha hmem
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    apply hab
    have h2 : Ψ a * Ψ (x * (c⁻¹ * b * c) * x⁻¹) = Ψ (x * (c⁻¹ * b * c) * x⁻¹) * Ψ a := by
      rw [← map_mul, ← map_mul, h1]
    rwa [hΨ] at h2
  have hCn : C.Normal := ⟨fun u hu x => by
    have : x * u * x⁻¹ ∈ C.map (MulAut.conj x).toMonoidHom := ⟨u, hu, rfl⟩
    rwa [hnorm x] at this⟩
  refine ⟨hCn, fun x => ?_⟩
  obtain ⟨c, hc, hxc⟩ := hrange x
  refine ⟨c, hc, ?_⟩
  have hne : (Ψ.comp C.subtype).ker ≠ ⊤ := by
    intro htop
    apply hab
    have h0 : (⟨a, ha⟩ : ↥C) ∈ (Ψ.comp C.subtype).ker := htop ▸ Subgroup.mem_top _
    have h1 : Ψ a = 1 := h0
    rw [h1, one_mul, mul_one]
  have hcen := CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hC.2.2
    (MonoidHom.normal_ker _) hne
  have key := conj_eq_of_conj_mem_center hC.2.2.1 (z := c⁻¹ * x) fun u hu => by
    have hwC : c⁻¹ * x * u * (c⁻¹ * x)⁻¹ ∈ C := hCn.conj_mem u hu _
    have hker : Ψ (c⁻¹ * x * u * (c⁻¹ * x)⁻¹ * u⁻¹) = 1 := by
      simp only [map_mul, map_inv, hxc]
      group
    have hwu : (⟨_, C.mul_mem hwC (C.inv_mem hu)⟩ : ↥C) ∈ Subgroup.center ↥C :=
      hcen (MonoidHom.mem_ker.mpr hker)
    refine ⟨_, C.mul_mem hwC (C.inv_mem hu), fun v hv => ?_, by group⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hwu ⟨v, hv⟩)).symm
  intro u hu
  calc x * u * x⁻¹ = c * (c⁻¹ * x * u * (c⁻¹ * x)⁻¹) * c⁻¹ := by group
    _ = c * u * c⁻¹ := by rw [key u hu]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]

theorem conj_mem_block {Q : Type*} [Group Q] (S : ∀ j, Subgroup (G j)) (β : Q →* ∀ j, G j)
    (hpi : Subgroup.pi Set.univ S ≤ β.range) (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (j : ι) (q : Q) {u : G j} (hu : u ∈ S j) : β q j * u * (β q j)⁻¹ ∈ S j := by
  have hsingle : Pi.mulSingle j u ∈ Subgroup.pi Set.univ S := by
    rw [Subgroup.mem_pi]
    intro k _
    by_cases hk : k = j
    · subst hk
      simpa using hu
    · simp [Pi.mulSingle_eq_of_ne hk]
  obtain ⟨q', hq'⟩ := hpi hsingle
  have hc := hcomm (Subgroup.commutator_mem_commutator ⟨q, rfl⟩ ⟨q', rfl⟩)
  have hcj := (Subgroup.mem_pi Set.univ).mp hc j (Set.mem_univ j)
  have hu' : β q' j = u := by rw [hq']; simp
  have heq : β q j * u * (β q j)⁻¹ = ⁅β q, β q'⁆ j * u := by
    rw [commutatorElement_def]
    simp only [Pi.mul_apply, Pi.inv_apply, hu']
    group
  rw [heq]
  exact (S j).mul_mem hcj hu

theorem isFiveComponent_normal_inner {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hPL : P ≤ L) {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) [∀ j, Finite (G j)] (S : ∀ j, Subgroup (G j))
    (β : ↥((P.subgroupOf L).comap ρ) →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (hpi : Subgroup.pi Set.univ S ≤ β.range) (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    (hinn : ∀ j, Open.IsQuasisimple (S j) → Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 →
      ∀ q, ∃ s ∈ S j, ∀ u ∈ S j, β q j * u * (β q j)⁻¹ = s * u * s⁻¹)
    {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (hC : IsFiveComponent P C) :
    C.Normal ∧ ∀ x, ∃ c ∈ C, ∀ u ∈ C, x * u * x⁻¹ = c * u * c⁻¹ := by
  classical
  obtain ⟨φ, hφ, hsolv, -⟩ := exists_quotient_of_cover hPL ρ hρ hker
  obtain ⟨hCc, f, hf⟩ := hC
  obtain ⟨j, hq, h60, hle⟩ := exists_block_of_comap S β hβ hpi hcomm hS φ hφ hCc.2.1 f hf
  set R := (Pi.evalMonoidHom G j).comp β with hR
  have hRS : ∀ q, ∀ u ∈ S j, R q * u * (R q)⁻¹ ∈ S j := fun q u hu =>
    conj_mem_block S β hpi hcomm j q hu
  have hlift : ∀ s ∈ S j, ∃ d ∈ C.comap φ, R d = s := by
    intro s hs
    obtain ⟨_, ⟨d, hd, rfl⟩, hds⟩ := hle hs
    exact ⟨d, hd, hds⟩
  set N : Subgroup ↥R.range := (Subgroup.centralizer (S j : Set (G j))).subgroupOf R.range
    with hN
  haveI hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
    obtain ⟨q, hq⟩ := g.2
    intro u hu
    have hu' : (R q)⁻¹ * u * R q ∈ S j := by
      have := hRS q⁻¹ u hu
      simpa [map_inv] using this
    have h1 := hn _ hu'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hq]
    calc u * (R q * (n : G j) * (R q)⁻¹)
        = R q * ((R q)⁻¹ * u * R q * (n : G j)) * (R q)⁻¹ := by group
      _ = R q * ((n : G j) * ((R q)⁻¹ * u * R q)) * (R q)⁻¹ := by rw [h1]
      _ = R q * (n : G j) * (R q)⁻¹ * u := by group⟩
  set Ψ₀ := (QuotientGroup.mk' N).comp R.rangeRestrict with hΨ₀
  have hkerle : φ.ker ≤ Ψ₀.ker := by
    intro n hn
    rw [MonoidHom.mem_ker, hΨ₀, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf, MonoidHom.coe_rangeRestrict,
      Subgroup.mem_centralizer_iff]
    set D := φ.ker.map R with hD
    haveI : Group.IsSolvable ↥D := solvable_of_surjective (R.subgroupMap_surjective φ.ker)
    have hDn : (D.subgroupOf (S j)).Normal := ⟨fun d hd s => by
      rw [Subgroup.mem_subgroupOf] at hd ⊢
      obtain ⟨k, hk, hkd⟩ := hd
      obtain ⟨_, ⟨q', -, rfl⟩, hq'⟩ := hle s.2
      refine ⟨q' * k * q'⁻¹, (MonoidHom.normal_ker φ).conj_mem k hk q', ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hkd]
      rw [show R q' = (s : G j) from hq']⟩
    have hDne : D.subgroupOf (S j) ≠ ⊤ := by
      intro htop
      apply LeviBlock.spFlag_not_isSolvable hq
      have hSD : S j ≤ D := fun s hs => by
        have : (⟨s, hs⟩ : ↥(S j)) ∈ D.subgroupOf (S j) := htop ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      exact solvable_of_solvable_injective (f := Subgroup.inclusion hSD)
        (Subgroup.inclusion_injective _)
    have hDc := CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq hDn hDne
    have hfix := conj_eq_of_conj_mem_center hq.1 (z := R n) fun u hu => by
      obtain ⟨q', -, hq'⟩ := hlift u hu
      have hw : R n * u * (R n)⁻¹ * u⁻¹ ∈ D := by
        refine ⟨n * q' * n⁻¹ * q'⁻¹, ?_, ?_⟩
        · have := (MonoidHom.normal_ker φ).conj_mem n⁻¹ (φ.ker.inv_mem hn) q'
          simpa [mul_assoc] using φ.ker.mul_mem hn this
        · simp only [map_mul, map_inv, hq']
      have hwS : R n * u * (R n)⁻¹ * u⁻¹ ∈ S j :=
        (S j).mul_mem (hRS n u hu) ((S j).inv_mem hu)
      have hwc : (⟨_, hwS⟩ : ↥(S j)) ∈ Subgroup.center ↥(S j) :=
        hDc (Subgroup.mem_subgroupOf.mpr hw)
      refine ⟨_, hwS, fun v hv => ?_, by group⟩
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨v, hv⟩)).symm
    intro u hu
    have := hfix u hu
    calc u * R n = R n * u * (R n)⁻¹ * R n := by rw [this]
      _ = R n * u := by group
  set Ψ := φ.liftOfSurjective hφ ⟨Ψ₀, hkerle⟩ with hΨ
  have hΨφ : ∀ q, Ψ (φ q) = Ψ₀ q := fun q => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hΨmk : ∀ q, Ψ (φ q) = QuotientGroup.mk (R.rangeRestrict q) := hΨφ
  refine normal_and_inner_of_map hCc Ψ ?_ ?_
  ·
    obtain ⟨a, b, hab⟩ := LeviBlock.exists_noncomm_centerQuotient hq
    obtain ⟨s₁, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨s₂, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨d₁, hd₁, hRd₁⟩ := hlift s₁ s₁.2
    obtain ⟨d₂, hd₂, hRd₂⟩ := hlift s₂ s₂.2
    refine ⟨φ d₁, hd₁, φ d₂, hd₂, fun h => hab ?_⟩
    rw [hΨmk, hΨmk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_center_iff]
    intro v
    have h1 := h v v.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.coe_rangeRestrict, hRd₁, hRd₂] at h1
    apply Subtype.ext
    simpa using h1
  ·
    intro x
    obtain ⟨q, rfl⟩ := hφ x
    obtain ⟨s, hs, hsq⟩ := hinn j hq h60 q
    obtain ⟨d, hd, hRd⟩ := hlift s hs
    refine ⟨φ d, hd, ?_⟩
    rw [hΨmk, hΨmk, QuotientGroup.eq, hN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := hsq u hu
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.coe_rangeRestrict, hRd]
    change u * ((R q)⁻¹ * s) = (R q)⁻¹ * s * u
    have h2 : R q * u * (R q)⁻¹ = s * u * s⁻¹ := h1
    calc u * ((R q)⁻¹ * s) = (R q)⁻¹ * (R q * u * (R q)⁻¹) * s := by group
      _ = (R q)⁻¹ * (s * u * s⁻¹) * s := by rw [h2]
      _ = (R q)⁻¹ * s * u := by group

end LeviFive

end CFSG.AGLEmbedding

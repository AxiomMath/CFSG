module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsFix
import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4

private theorem fix_of_comm_central {H : Type*} [Group H] {I : Subgroup H}
    (hperf : commutator ↥I = ⊤) (ψ : MulAut H) (hψ : ∀ j ∈ I, ψ j ∈ I)
    (hc : ∀ j ∈ I, ∀ k ∈ I, (j * (ψ j)⁻¹) * k = k * (j * (ψ j)⁻¹)) : ∀ j ∈ I, ψ j = j := by
  have hmem : ∀ j : ↥I, (j : H) * (ψ j)⁻¹ ∈ I := fun j =>
    I.mul_mem j.2 (I.inv_mem (hψ j j.2))
  have hcen : ∀ j : ↥I, (⟨_, hmem j⟩ : ↥I) ∈ Subgroup.center ↥I := fun j =>
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hc j j.2 k k.2).symm
  let δ : ↥I →* ↥(Subgroup.center ↥I) :=
    { toFun := fun j => ⟨⟨_, hmem j⟩, hcen j⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        simp
      map_mul' := fun j k => by
        apply Subtype.ext; apply Subtype.ext
        have hk := hc k k.2 (ψ j)⁻¹ (I.inv_mem (hψ j j.2))
        show (j : H) * k * (ψ (j * k))⁻¹ = (j : H) * (ψ j)⁻¹ * ((k : H) * (ψ k)⁻¹)
        rw [map_mul, mul_inv_rev]
        calc (j : H) * k * ((ψ k)⁻¹ * (ψ j)⁻¹) = j * ((k * (ψ k)⁻¹) * (ψ j)⁻¹) := by group
          _ = j * ((ψ j)⁻¹ * (k * (ψ k)⁻¹)) := by rw [hk]
          _ = j * (ψ j)⁻¹ * (k * (ψ k)⁻¹) := by group }
  have hker : commutator ↥I ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hperf] at hker
  intro j hj
  have h1 : δ ⟨j, hj⟩ = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top _))
  have h2 : (j : H) * (ψ j)⁻¹ = 1 := congrArg (fun y : ↥(Subgroup.center ↥I) => ((y : ↥I) : H)) h1
  exact (mul_inv_eq_one.mp h2).symm

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_lift (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {H : Type} [Group H] [Finite H] (φ : H →* Ω) (hφS : φ.range = S)
    (hker : φ.ker ≤ Subgroup.center H) (hkerp : Nat.Coprime (Nat.card φ.ker) p)
    (lift : ↥B → MulAut H)
    (hlift : ∀ (x : ↥B) (h : H), φ (lift x h) = (x : Ω) * φ h * (x : Ω)⁻¹)
    {D E : Subgroup Ω} (hDB : D ≤ B) (hEB : E ≤ B) (hDE : D ≤ E) (hDc : p ^ 2 ≤ Nat.card D)
    (hDBc : p ^ 2 * Nat.card D ≤ Nat.card B) (hEc : Nat.card D = p ^ 2 → Nat.card E = p ^ 3)
    {I : Subgroup H}
    (hI : GLAPComponent p (ModelGen.fixFam fun x : {x : ↥B // (x : Ω) ∈ D} => lift x.1) I)
    (hIq : CFSG.Open.IsQuasisimple ↥I) (hpI : p ∣ Nat.card I)
    (hIB : ∀ x : ↥B, I.map (lift x).toMonoidHom = I)
    (hID : ∀ x : ↥B, (∀ j ∈ I, lift x j = j) → (x : Ω) ∈ D)
    (hIE : Nat.card D = p ^ 2 →
      GLAPLayer p (I ⊓ ModelGen.fixFam fun x : {x : ↥B // (x : Ω) ∈ E} => lift x.1) ≠ ⊥)
    {z : H} (hz1 : φ z ≠ 1) (hz2 : z ^ 2 = 1) (hzI : ∀ j ∈ I, j * z = z * j)
    (hzD : ∀ x : ↥B, (x : Ω) ∈ D → lift x z = z) : S267ConcA p S B := by
  classical
  let π : H →* ↥S := φ.codRestrict S fun h => by rw [← hφS]; exact ⟨h, rfl⟩
  have hπφ : ∀ h, (π h : Ω) = φ h := fun h => rfl
  have hπsurj : Function.Surjective π := by
    rintro ⟨s, hs⟩
    rw [← hφS] at hs
    obtain ⟨h, rfl⟩ := hs
    exact ⟨h, rfl⟩
  have hπker : π.ker = φ.ker := by
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Subtype.val_inj]
    rfl
  have hπkerC : π.ker ≤ Subgroup.center H := hπker ▸ hker
  let α : ↥B → MulAut ↥S := fun x => MulAut.conjNormal (x : Ω)
  have hα : ∀ (x : ↥B) (g : ↥S), (x : Ω) * S.subtype g * (x : Ω)⁻¹ = S.subtype (α x g) :=
    fun x g => by simp [α, MulAut.conjNormal_apply]
  have hαβ : ∀ (x : ↥B) (h : H), π (lift x h) = α x (π h) := by
    intro x h
    apply Subtype.ext
    rw [hπφ, hlift]
    simp [α, MulAut.conjNormal_apply, hπφ]
  have hfixE : ∀ F : Subgroup Ω,
      ModelGen.fixFam (fun x : {x : ↥B // (x : Ω) ∈ F} => α x.1) = ModelGen.actFix α F := by
    intro F
    ext g
    rw [ModelGen.mem_fixFam, ModelGen.mem_actFix]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
  have hJ : GLAPComponent p (ModelGen.actFix α D) (I.map π) := by
    have h := ModelGen.glaPComponent_map_inf_fixFam π hπkerC
      (fun x : {x : ↥B // (x : Ω) ∈ D} => lift x.1) (fun x => α x.1) (fun x h => hαβ x.1 h) hp
      ⊤ (by rw [top_inf_eq]; exact hI)
    rwa [Subgroup.map_top_of_surjective π hπsurj, top_inf_eq, hfixE] at h
  have hJB : ∀ x : ↥B, (I.map π).map (α x).toMonoidHom = I.map π := by
    intro x
    rw [Subgroup.map_map]
    have e : (α x).toMonoidHom.comp π = π.comp (lift x).toMonoidHom := by
      ext h
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact congrArg Subtype.val (hαβ x h).symm
    rw [e, ← Subgroup.map_map, hIB x]
  have hIperf : Group.IsPerfect ↥I := ⟨hIq.1⟩
  have hkerI : (π.subgroupMap I).ker ≤ Subgroup.center ↥I := by
    intro y hy
    have hy' : (y : H) ∈ π.ker := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      exact MonoidHom.mem_ker.mpr this
    exact Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hπkerC hy') k)
  have hnp : ¬ p ∣ Nat.card φ.ker := (Nat.Prime.coprime_iff_not_dvd hp).mp hkerp.symm
  have hpJ : p ∣ Nat.card ↥(I.map π) := by
    have hcard := Subgroup.card_ker_mul_card_range (π.subgroupMap I)
    rw [MonoidHom.range_eq_top.mpr (π.subgroupMap_surjective I), Subgroup.card_top] at hcard
    have hle : ((π.subgroupMap I).ker).map I.subtype ≤ φ.ker := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← hπker, MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have hkdvd : Nat.card (π.subgroupMap I).ker ∣ Nat.card φ.ker := by
      rw [← Subgroup.card_map_of_injective I.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    rw [← hcard] at hpI
    rcases (Nat.Prime.dvd_mul hp).mp hpI with h | h
    · exact absurd (h.trans hkdvd) hnp
    · exact h
  have hJq : CFSG.IsQuasisimple ↥(I.map π) := by
    have hIq' : CFSG.IsQuasisimple ↥I :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥I).mp hIq
    refine CFSG.LocalCores.isQuasisimple_map hIq' π fun hle => hnp ?_
    rw [← hπker]
    exact hpI.trans (Subgroup.card_dvd_of_le hle)
  have hOcent : ∀ o ∈ GLAPPrimeCoreOf p (I.map π), ∀ j ∈ I.map π, o * j = j * o := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJq (GLAPPrimeCore.normal p ↥(I.map π))
      with h | h
    · exfalso
      have hc := CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p
        ↥(I.map π)
      rw [h, Subgroup.card_top] at hc
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hc hpJ
    · intro o ho j hj
      unfold GLAPPrimeCoreOf at ho
      obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.1 ho
      exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp (h ho')) ⟨j, hj⟩)).symm
  have hJD : ∀ x : ↥B, (∀ j ∈ I.map π, j * (α x j)⁻¹ ∈ GLAPPrimeCoreOf p (I.map π)) →
      (x : Ω) ∈ D := by
    intro x hx
    apply hID x
    have hmapI : ∀ j ∈ I, lift x j ∈ I := fun j hj => by
      rw [← hIB x]
      exact ⟨j, hj, rfl⟩
    refine fix_of_comm_central hIq.1 (lift x) hmapI fun j hj k hk => ?_
    have hg : j * (lift x j)⁻¹ ∈ I := I.mul_mem hj (I.inv_mem (hmapI j hj))
    have hπg : π (j * (lift x j)⁻¹) ∈ GLAPPrimeCoreOf p (I.map π) := by
      rw [map_mul, map_inv, hαβ]
      exact hx (π j) ⟨j, hj, rfl⟩
    have hcJ : (π.subgroupMap I) ⟨_, hg⟩ ∈ Subgroup.center ↥(I.map π) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (hOcent _ hπg y y.2).symm
    have hcI : (⟨_, hg⟩ : ↥I) ∈ Subgroup.center ↥I := by
      rw [← CFSG.LocalCores.comap_center_eq_of_perfect hIperf (π.subgroupMap I)
        (π.subgroupMap_surjective I) hkerI]
      exact hcJ
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hcI) ⟨k, hk⟩)).symm
  have hJE : Nat.card D = p ^ 2 → GLAPLayer p (I.map π ⊓ ModelGen.actFix α E) ≠ ⊥ := by
    intro hD2
    have h := (ModelGen.glaPLayer_inf_fixFam_ne_bot_iff π hπkerC
      (fun x : {x : ↥B // (x : Ω) ∈ E} => lift x.1) (fun x => α x.1) (fun x h => hαβ x.1 h)
      hp I).mp (hIE hD2)
    rwa [hfixE] at h
  have ht1 : π z ≠ 1 := fun h => hz1 (by rw [← hπφ, h]; rfl)
  have ht2 : π z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have htJ : I.map π ≤ Subgroup.centralizer ({π z} : Set ↥S) := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hzI j hj]
  have htD : ∀ x : ↥B, (x : Ω) ∈ D → α x (π z) = π z := fun x hx => by
    rw [← hαβ, hzD x hx]
  exact ModelGen.concA_of_action hp hB hBC S.subtype S.subtype_injective S.range_subtype α hα
    hDB hEB hDE hDc hDBc hEc hJ hJB hJD hJE ht1 ht2 htJ htD

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

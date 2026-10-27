module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Ker
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Da

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G}
  {K1 K2 : Subgroup G} {g : G}

theorem sec10B_toA2Ctx (hb : Asc82Basic10) (hctx : Sec109Ctx G t L S z K1 K2 g) :
    Sec10A2Ctx G t L S z K1 K2 g := by
  obtain ⟨-, hz2, -, -, -, -⟩ := sec10D_basic hb hctx.toSec10Ctx
  have hgz : g * z = z * g := sec10D_g_comm_z hz2 hctx
  have hfix : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group
  exact
    { toSec10Ctx := hctx.toSec10Ctx
      norm := hctx.norm
      not_M := hctx.not_M
      two := hctx.two
      swap_t := hctx.swap
      fix_z := hfix }

theorem sec10B_comm (hf : Asc82Facts10) (hb : Asc82Basic10) (hctx : Sec10Ctx G t L S z K1 K2) :
    ⁅K1, K2⁆ = ⊥ := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  exact Subgroup.mem_centralizer_iff.mpr fun b hb' =>
    (sec10Z_comm hf.pockets5 hpsp hctx a ha b hb').symm

theorem sec10B_act_z (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g)
    {f : ↥(S ⊔ zpowers g) →* MulAut ↥(K1 ⊔ K2)} (hfs : Sec10A2Act t z K1 K2 (S ⊔ zpowers g) f) :
    ∀ y : ↥(S ⊔ zpowers g), (y : G) ∈ zpowers z → f y = 1 := by
  have hD := sec10A2_split h3 h hf hb hctx.toSec10Ctx
  have hzT : z ∈ S ⊔ zpowers g := Subgroup.mem_sup_left hctx.mem_S
  have hKC : K1 ⊔ K2 ≤ centralizer ({z} : Set G) :=
    sup_le (hctx.pocket1.2.1.trans inf_le_right) (hctx.pocket2.2.1.trans inf_le_right)
  have hfz : f ⟨z, hzT⟩ = 1 := by
    refine (hD.act_eq_one_iff f hfs ⟨z, hzT⟩).mpr fun k hk => ?_
    have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
    have e : z * k * z⁻¹ * k⁻¹ = 1 := by
      rw [← hkz]
      group
    show z * k * z⁻¹ * k⁻¹ ∈ oddCoreIn (secK0 t z)
    rw [e]
    exact Subgroup.one_mem _
  intro y hy
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hyz : y = (⟨z, hzT⟩ : ↥(S ⊔ zpowers g)) ^ n := Subtype.ext (by rw [← hn]; simp)
  rw [hyz, map_zpow, hfz, one_zpow]

theorem sec10B_t_mem_conj (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hr : Asc82FactRankK5) (hb : Asc82Basic10) (hctx : Sec109Ctx G t L S z K1 K2 g) {c : G}
    (hc : c ∈ centralizer ({z} : Set G))
    (hle : CFSG.conjugate (secW t K1 K2) c ≤ S ⊔ zpowers g) : c * t * c⁻¹ ∈ secW t K1 K2 := by
  by_contra htn
  have hctxA := sec10B_toA2Ctx hb hctx
  obtain ⟨f, hfs⟩ := sec10A2_exists_act h3 h hf hb hctxA
  obtain ⟨hzW, hWmod⟩ := sec10J_W_elem hf.pockets5 hf.centZ5 hb hctx.toSec10Ctx
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  set U : Subgroup G := CFSG.conjugate (secW t K1 K2) c with hU
  have htU : t ∉ U := fun hmem => htn (mem_conjugate_iff'.mp hmem)
  have hzU : z ∈ U := by
    refine mem_conjugate_iff'.mpr ?_
    have e : c * z * c⁻¹ = z := by rw [hcz]; group
    rw [e]
    exact hzW
  have hel : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ zpowers z ∧ a * a ∈ zpowers z := by
    intro a ha b hb'
    obtain ⟨h1, h2⟩ := hWmod _ (mem_conjugate_iff'.mp ha) _ (mem_conjugate_iff'.mp hb')
    refine ⟨sec10B_mem_zpowers_of_conj hcz ?_, sec10B_mem_zpowers_of_conj hcz ?_⟩
    · have e : c * (a * b * a⁻¹ * b⁻¹) * c⁻¹ =
          (c * a * c⁻¹) * (c * b * c⁻¹) * (c * a * c⁻¹)⁻¹ * (c * b * c⁻¹)⁻¹ := by group
      rw [e]
      exact h1
    · have e : c * (a * a) * c⁻¹ = (c * a * c⁻¹) * (c * a * c⁻¹) := by group
      rw [e]
      exact h2
  let φ : ↥U →* MulAut ↥(K1 ⊔ K2) := f.comp (Subgroup.inclusion hle)
  have hφ1 : ∀ x : ↥U, (x : G) ∈ zpowers z → φ x = 1 := fun x hx =>
    sec10B_act_z h3 h hf hb hctxA hfs ⟨(x : G), hle x.2⟩ hx
  have hE : CFSG.Open.IsElemAbelian 2 φ.range :=
    sec10B_range_isElemAbelian φ (fun a b => hφ1 _ (hel a a.2 b b.2).1)
      (fun a => hφ1 _ (hel a a.2 a a.2).2)
  have hker : Nat.card ↥φ.ker ≤ 2 := by
    classical
    have hmem : ∀ u : ↥φ.ker, ((u : ↥U) : G) ∈ ({1, z} : Finset G) := by
      intro u
      have hu1 : f ⟨((u : ↥U) : G), hle (u : ↥U).2⟩ = 1 := u.2
      have hS : ((u : ↥U) : G) ∈ S :=
        sec10A2_ker_le_S h3 h hf hb hctxA hfs (y := ⟨((u : ↥U) : G), hle (u : ↥U).2⟩) hu1
      have h4 : ((u : ↥U) : G) = 1 ∨ ((u : ↥U) : G) = t ∨ ((u : ↥U) : G) = z ∨
          ((u : ↥U) : G) = t * z :=
        sec10A2_ker_S h3 h hf hb hctxA hfs (u := ⟨((u : ↥U) : G), hle (u : ↥U).2⟩) hS hu1
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h4 with h4 | h4 | h4 | h4
      · exact Or.inl h4
      · exact absurd (h4 ▸ (u : ↥U).2) htU
      · exact Or.inr h4
      · exfalso
        refine htU ?_
        have := U.mul_mem (h4 ▸ (u : ↥U).2) (U.inv_mem hzU)
        rwa [mul_inv_cancel_right] at this
    have hinj : Function.Injective (fun u : ↥φ.ker =>
        (⟨((u : ↥U) : G), hmem u⟩ : ↥({1, z} : Finset G))) := by
      intro u v huv
      have h' := congrArg Subtype.val huv
      exact Subtype.ext (Subtype.ext h')
    calc Nat.card ↥φ.ker ≤ Nat.card ↥({1, z} : Finset G) := Nat.card_le_card_of_injective _ hinj
      _ = ({1, z} : Finset G).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ 2 := Finset.card_le_two
  have hU64 : 64 ≤ Nat.card ↥U := by
    rw [hU, sec10B_card_conjugate]
    exact sec10B_card_W hf.pockets5 hf.centZ5 hb hctx.toSec10Ctx
  have hrange := sec10B_card_range_ge φ hker hU64
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  obtain ⟨e1, e2⟩ := sec10KS_equiv hf.pockets5 hf.centZ5 hpsp hctx.toSec10Ctx
  have hbound := hr G K1 K2 (sec10B_comm hf hb hctx.toSec10Ctx)
    (sec10KS_card_sup hf.pockets5 hf.centZ5 hpsp hctx.toSec10Ctx) e1 e2 φ.range hE
  omega

end CFSG.OddStandard.SmallF3.Omega

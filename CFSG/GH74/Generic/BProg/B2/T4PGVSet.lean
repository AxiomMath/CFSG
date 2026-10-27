module

public import CFSG.GH74.Generic.BProg.B2.T4PGVDefs
public import CFSG.GH74.Generic.BProg.B2.T4P151V

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.RankThree.PerfectCover Subgroup

theorem card_hopfMultiplier_of_q3
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {Y : Type} [Group Y]
    (h : LieModel Y .PSL 3 3 1) : Nat.card (hopfMultiplier Y) = 1 := by
  have hm' : CFSG.Models.LieModel Y .PSL 3 3 1 := models_of_blueprint_of_ne_zero (by norm_num) h
  rw [S3.card_hopfMultiplier_psl_three hGA (by norm_num) hm']
  norm_num

theorem center_eq_bot_of_q3
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {J : Type} [Group J]
    [Finite J] (hJ : IsQuasisimple J) (h : LieModel (J ⧸ center J) .PSL 3 3 1) :
    center J = ⊥ := by
  have hd := card_center_dvd_hopfMultiplier hJ (MulEquiv.refl _)
  rw [card_hopfMultiplier_of_q3 hGA h, Nat.dvd_one] at hd
  exact Subgroup.eq_bot_of_card_eq _ hd

section Vert

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {σ : X}

theorem exists_q3Cent_of_vert
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (hL : IsComponent L)
    (hσσ : σ * σ = 1) (hLσ : L.map (MulAut.conj σ).toMonoidHom = L)
    (hnt : ∃ l ∈ L, l * σ ≠ σ * l) {J : Subgroup X}
    (hJ : IsCompIn (centralizer ({σ} : Set X)) J) (hJL : J ≤ L)
    (hQ : LieModel (↥J ⧸ center ↥J) .PSL 3 3 1)
    {e₁ e₂ : X} (he₁ : e₁ ∈ J) (he₂ : e₂ ∈ J) (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1)
    (h₁1 : e₁ ≠ 1) (h₂1 : e₂ ≠ 1) (hne : e₁ ≠ e₂) :
    ∃ (N : Type) (_ : Group N) (_ : Finite N) (H : Subgroup N) (t : N) (K : Subgroup N),
      Q3Cent H t K ∧ Nonempty (↥L ⧸ center ↥L ≃* ↥H) := by
  classical
  set H₀ := ↥L ⧸ center ↥L with hH₀
  have hsimple : IsSimpleGroup H₀ := hL.1.2.1
  have hZ : ∀ z : H₀, (∀ g : H₀, g * z = z * g) → z = 1 := by
    intro z hz
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H₀) with hb | ht
    · have : z ∈ center H₀ := Subgroup.mem_center_iff.2 hz
      rw [hb] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      obtain ⟨a, b, hab⟩ := hL.1.2.2
      apply hab
      have : b ∈ center H₀ := ht ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.1 this a)
  have hinj : Function.Injective (MulAut.conj : H₀ →* MulAut H₀) :=
    GenLocBasic.conj_injective_of_center_trivial hZ
  have : Finite (MulAut H₀) :=
    Finite.of_injective (fun φ : MulAut H₀ => (φ : H₀ → H₀))
      (fun a b h => MulEquiv.ext (congrFun h))
  set H : Subgroup (MulAut H₀) := (MulAut.conj : H₀ →* MulAut H₀).range with hH
  set eH : H₀ ≃* ↥H := MonoidHom.ofInjective hinj with heH
  set π := QuotientGroup.mk' (center ↥L) with hπ
  set Jb : Subgroup H₀ := (J.subgroupOf L).map π with hJbdef
  set K : Subgroup (MulAut H₀) := Jb.map MulAut.conj with hK
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  have hJc := P151V.isCompIn_fixTau hLσ hJ hJL
  have hJq : IsQuasisimple ↥J := Prop31.isQuasisimple_of_isCompIn hJ
  have hJZ := center_eq_bot_of_q3 hGA hJq hQ
  set ρ : ↥J →* ↥Jb := (π.comp (Subgroup.inclusion hJL)).codRestrict Jb
    (fun j => ⟨Subgroup.inclusion hJL j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩) with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩
    exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩
  have hρi : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h1 : π (Subgroup.inclusion hJL j) = 1 := congrArg Subtype.val hj
    have h2 : Subgroup.inclusion hJL j ∈ center ↥L := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : j ∈ center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h4 := Subgroup.mem_center_iff.1 h2 (Subgroup.inclusion hJL g)
      have h5 : ((g * j : ↥J) : X) = ((j * g : ↥J) : X) := congrArg (fun y : ↥L => (y : X)) h4
      exact Subtype.ext h5
    rw [hJZ] at h3
    exact Subgroup.mem_bot.1 h3
  set ψ : ↥J ≃* ↥K :=
    (MulEquiv.ofBijective ρ ⟨hρi, hρs⟩).trans (Jb.equivMapOfInjective _ hinj) with hψ
  have eJ : ↥J ⧸ center ↥J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hJZ).trans QuotientGroup.quotientBot
  refine ⟨MulAut H₀, inferInstance, inferInstance, H, P151V.tau hLσ, K, ?_, ⟨eH⟩⟩
  refine ⟨P151V.inn_normal, (MulEquiv.isSimpleGroup_congr eH).1 hsimple,
    P151V.eq_one_of_comm_inn hinj, P151V.orderOf_tau hLσ hσσ hperf hnt, ?_, ?_, ?_⟩
  · rw [← P151V.map_conj_fixTau hLσ hinj]
    exact B3aG.isCompIn_map_of_injective hinj hJc
  ·
    have hi : ∀ x : ↥J, x * x = 1 → ((ψ x : ↥K) : MulAut H₀) * ψ x = 1 := fun x hx => by
      rw [← Subgroup.coe_mul, ← map_mul, hx, map_one, Subgroup.coe_one]
    have hn : ∀ x : ↥J, x ≠ 1 → ((ψ x : ↥K) : MulAut H₀) ≠ 1 := fun x hx h => hx
      (ψ.injective (Subtype.ext (by rw [h, map_one, Subgroup.coe_one])))
    refine ⟨ψ ⟨e₁, he₁⟩, (ψ ⟨e₁, he₁⟩).2, ψ ⟨e₂, he₂⟩, (ψ ⟨e₂, he₂⟩).2,
      hi _ (Subtype.ext h₁), hi _ (Subtype.ext h₂), hn _ (fun h => h₁1 (congrArg Subtype.val h)),
      hn _ (fun h => h₂1 (congrArg Subtype.val h)), fun h => hne ?_⟩
    exact congrArg Subtype.val (ψ.injective (Subtype.ext h))
  · exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (eJ.trans ψ) hQ

end Vert

end CFSG.GH74.Generic.BProg.B2.T4.PGV

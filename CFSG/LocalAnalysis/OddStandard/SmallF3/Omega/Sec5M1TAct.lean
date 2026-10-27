module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

private theorem sec5m1t_aux_normalizer {φ : ↥L →* omegaGroup hQ} {s : G} {x : simGroup Q}
    (h : CoverAct L φ s x) : s ∈ Subgroup.normalizer (L : Set G) := by
  with_unfolding_all exact h.1

private theorem sec5m1t_aux_apply {φ : ↥L →* omegaGroup hQ} {s : G} {x : simGroup Q}
    (h : CoverAct L φ s x) {l l' : ↥L} (hl : (l' : G) = s * l * s⁻¹) :
    ((φ l' : omegaGroup hQ) : OGroup Q) =
      simAct Q x ((φ l : omegaGroup hQ) : OGroup Q) := by
  with_unfolding_all exact h.2 l l' hl

theorem sec5m1t_coverAct_sq {φ : ↥L →* omegaGroup hQ} {c : G} {x : simGroup Q}
    (hx : CoverAct L φ c x) {l l₂ : ↥L} (hl₂ : (l₂ : G) = (c * c) * (l : G) * (c * c)⁻¹) :
    ((φ l₂ : omegaGroup hQ) : OGroup Q) =
      simAct Q (x * x) ((φ l : omegaGroup hQ) : OGroup Q) := by
  have hc : c ∈ Subgroup.normalizer (L : Set G) := sec5m1t_aux_normalizer hx
  let l₁ : ↥L := ⟨c * (l : G) * c⁻¹,
    (Subgroup.mem_normalizer_iff.mp hc (l : G)).mp l.2⟩
  have hl₁ : ((φ l₁ : omegaGroup hQ) : OGroup Q) =
      simAct Q x ((φ l : omegaGroup hQ) : OGroup Q) := sec5m1t_aux_apply hx rfl
  let l₂' : ↥L := ⟨c * (l₁ : G) * c⁻¹,
    (Subgroup.mem_normalizer_iff.mp hc (l₁ : G)).mp l₁.2⟩
  have hl₂' : ((φ l₂' : omegaGroup hQ) : OGroup Q) =
      simAct Q x ((φ l₁ : omegaGroup hQ) : OGroup Q) := sec5m1t_aux_apply hx rfl
  have hEq : l₂' = l₂ := by
    apply Subtype.ext
    show c * (l₁ : G) * c⁻¹ = (l₂ : G)
    rw [show (l₁ : G) = c * (l : G) * c⁻¹ from rfl, hl₂]
    group
  rw [← hEq, hl₂', hl₁, map_mul (simAct Q) x x, MulAut.mul_apply]

theorem sec5m1t_sq_act {φ : ↥L →* omegaGroup hQ} (hs : Function.Surjective φ) {z c : G}
    (hz : z ∈ L) {x : simGroup Q} (hx : CoverAct L φ c x)
    (hcz : ∀ y ∈ L, (c * c) * y * (c * c)⁻¹ = z * y * z⁻¹) :
    ∀ t ∈ omegaGroup hQ, simAct Q (x * x) t =
      simAct Q (orthToSim Q ((φ ⟨z, hz⟩ : omegaGroup hQ) : OGroup Q)) t := by
  intro t ht
  obtain ⟨l, hl⟩ := hs ⟨t, ht⟩
  have hlcoe : ((φ l : omegaGroup hQ) : OGroup Q) = t := congrArg Subtype.val hl
  let l₂ : ↥L := ⟨z * (l : G) * z⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hz l.2) (Subgroup.inv_mem _ hz)⟩
  have hl₂ : (l₂ : G) = (c * c) * (l : G) * (c * c)⁻¹ := by
    show z * (l : G) * z⁻¹ = (c * c) * (l : G) * (c * c)⁻¹
    rw [hcz (l : G) l.2]
  have h1 := sec5m1t_coverAct_sq hx hl₂
  rw [hlcoe] at h1
  have h2 : ((φ l₂ : omegaGroup hQ) : OGroup Q) =
      simAct Q (orthToSim Q ((φ ⟨z, hz⟩ : omegaGroup hQ) : OGroup Q)) t := by
    have heq : l₂ = ⟨z, hz⟩ * l * ⟨z, hz⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [heq, map_mul φ, map_mul φ, map_inv φ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [simAct_orthToSim, hlcoe]
  exact h1.symm.trans h2

theorem sec5m1t_comm_odd {φ : ↥L →* omegaGroup hQ} (hφ : Function.Injective φ)
    (hs : Function.Surjective φ) {z c : G} (hz : z ∈ L) {x : simGroup Q}
    (hx : CoverAct L φ c x)
    (hodd : ∀ l : ↥L, z * (l : G) = (l : G) * z → Odd (orderOf (l : G)) →
      c * (l : G) = (l : G) * c) :
    ∀ h ∈ omegaGroup hQ,
      h * ((φ ⟨z, hz⟩ : omegaGroup hQ) : OGroup Q) =
        ((φ ⟨z, hz⟩ : omegaGroup hQ) : OGroup Q) * h → Odd (orderOf h) →
        x * orthToSim Q h = orthToSim Q h * x := by
  intro h hh hcomm hoddh
  obtain ⟨l, hl⟩ := hs ⟨h, hh⟩
  have hlco : ((φ l : omegaGroup hQ) : OGroup Q) = h := congrArg Subtype.val hl
  have hprod : φ (⟨z, hz⟩ * l) = φ (l * ⟨z, hz⟩) := by
    apply Subtype.ext
    rw [map_mul φ, map_mul φ, Subgroup.coe_mul, Subgroup.coe_mul, hl]
    exact hcomm.symm
  have hinj : ⟨z, hz⟩ * l = l * ⟨z, hz⟩ := hφ hprod
  have hcommG : z * (l : G) = (l : G) * z := by
    have h := congrArg (fun q : ↥L => (q : G)) hinj
    simpa only [Subgroup.coe_mul] using h
  have hoddL : Odd (orderOf (l : G)) := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective φ hφ l, ← Subgroup.orderOf_coe (φ l), hlco]
    exact hoddh
  have hc : c * (l : G) = (l : G) * c := hodd l hcommG hoddL
  have hfix : simAct Q x ((φ l : omegaGroup hQ) : OGroup Q) =
      ((φ l : omegaGroup hQ) : OGroup Q) := t5_cent_map_mem hx hc
  have hmul : (x : V ≃ₗ[ZMod 3] V) * (h : V ≃ₗ[ZMod 3] V) =
      (h : V ≃ₗ[ZMod 3] V) * (x : V ≃ₗ[ZMod 3] V) := by
    have hh' := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) hfix
    rw [coe_simAct, hlco] at hh'
    calc (x : V ≃ₗ[ZMod 3] V) * (h : V ≃ₗ[ZMod 3] V)
        = ((x : V ≃ₗ[ZMod 3] V) * (h : V ≃ₗ[ZMod 3] V)
            * (x : V ≃ₗ[ZMod 3] V)⁻¹) * (x : V ≃ₗ[ZMod 3] V) := by group
      _ = (h : V ≃ₗ[ZMod 3] V) * (x : V ≃ₗ[ZMod 3] V) := by rw [hh']
  exact Subtype.ext (by simpa only [Subgroup.coe_mul, coe_orthToSim] using hmul)

theorem sec5m1t_cent_equiv {φ : ↥L →* omegaGroup hQ} (hφ : Function.Injective φ)
    (hs : Function.Surjective φ) {d : G} {p : OGroup Q} (hd : CoverAct L φ d (orthToSim Q p)) :
    ∃ ψ : ↥(L ⊓ centralizer ({d} : Set G)) ≃*
        ↥(omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q))),
      ∀ y : ↥(L ⊓ centralizer ({d} : Set G)),
        ((ψ y : ↥(omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)))) : OGroup Q) =
          ((φ ⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩ : omegaGroup hQ) : OGroup Q) := by
  let Φ : ↥(L ⊓ centralizer ({d} : Set G)) →* omegaGroup hQ :=
    φ.comp (Subgroup.inclusion (inf_le_left : L ⊓ centralizer ({d} : Set G) ≤ L))
  have hΦinj : Function.Injective Φ := fun a b hab => Subgroup.inclusion_injective _ (hφ hab)
  have hΦmem : ∀ y : ↥(L ⊓ centralizer ({d} : Set G)),
      ((Φ y : omegaGroup hQ) : OGroup Q) ∈
        (omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q))) := by
    intro y
    obtain ⟨_, hyc⟩ := Subgroup.mem_inf.mp y.2
    refine Subgroup.mem_inf.mpr ⟨(Φ y).2, ?_⟩
    have hcommG : d * (y : G) = (y : G) * d :=
      (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
    have hcommG' : d * (↑(Subgroup.inclusion (inf_le_left :
          L ⊓ centralizer ({d} : Set G) ≤ L) y) : G) =
        (↑(Subgroup.inclusion (inf_le_left :
          L ⊓ centralizer ({d} : Set G) ≤ L) y) : G) * d := by
      simpa only [Subgroup.coe_inclusion] using hcommG
    have hfix := t5_cent_map_mem (φ := φ) (s := d) (x := orthToSim Q p) hd hcommG'
    change simAct Q (orthToSim Q p) ((Φ y : omegaGroup hQ) : OGroup Q) =
      ((Φ y : omegaGroup hQ) : OGroup Q) at hfix
    rw [simAct_orthToSim] at hfix
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((Φ y : omegaGroup hQ) : OGroup Q) * p
        = (p * ((Φ y : omegaGroup hQ) : OGroup Q) * p⁻¹) * p := by rw [hfix]
      _ = p * ((Φ y : omegaGroup hQ) : OGroup Q) := by group
  let ψ₀ : ↥(L ⊓ centralizer ({d} : Set G)) →*
      ↥(omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q))) :=
  { toFun := fun y => ⟨((Φ y : omegaGroup hQ) : OGroup Q), hΦmem y⟩
    map_one' := Subtype.ext (by
      change ((Φ 1 : omegaGroup hQ) : OGroup Q) = (1 : OGroup Q)
      rw [map_one Φ]
      rfl)
    map_mul' := fun a b => Subtype.ext (by
      change ((Φ (a * b) : omegaGroup hQ) : OGroup Q) =
        ((Φ a : omegaGroup hQ) : OGroup Q) * ((Φ b : omegaGroup hQ) : OGroup Q)
      rw [map_mul Φ a b, Subgroup.coe_mul]) }
  have hψ₀inj : Function.Injective ψ₀ := by
    intro a b hab
    apply hΦinj
    apply Subtype.ext
    have hab' : ((ψ₀ a : ↥(omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)))) : OGroup Q) =
        ((ψ₀ b : ↥(omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)))) : OGroup Q) :=
      congrArg Subtype.val hab
    exact hab'
  have hψ₀surj : Function.Surjective ψ₀ := by
    intro g
    obtain ⟨hgl, hgc⟩ := Subgroup.mem_inf.mp g.2
    obtain ⟨l, hl⟩ := hs ⟨g.val, hgl⟩
    have hlco : ((φ l : omegaGroup hQ) : OGroup Q) = g.val := congrArg Subtype.val hl
    let l' : ↥L := ⟨d * (l : G) * d⁻¹,
      (Subgroup.mem_normalizer_iff.mp (sec5m1t_aux_normalizer hd) (l : G)).mp l.2⟩
    have hpcomm : p * g.val = g.val * p :=
      (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm
    have hkey : ((φ l' : omegaGroup hQ) : OGroup Q) = g.val := by
      have h1 := sec5m1t_aux_apply (l := l) (l' := l') (φ := φ) (s := d)
        (x := orthToSim Q p) hd (show (l' : G) = d * (l : G) * d⁻¹ from rfl)
      rw [simAct_orthToSim] at h1
      rw [h1, hlco, hpcomm]
      group
    have hphi : φ l' = φ l := by
      apply Subtype.ext
      rw [hkey, hlco]
    have hl'eq : l' = l := hφ hphi
    have hconj : d * (l : G) * d⁻¹ = (l : G) :=
      congrArg (fun q : ↥L => (q : G)) hl'eq
    have hlcent : (l : G) ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (l : G) * d = (d * (l : G) * d⁻¹) * d := by rw [hconj]
        _ = d * (l : G) := by group
    refine ⟨⟨(l : G), Subgroup.mem_inf.mpr ⟨l.2, hlcent⟩⟩, Subtype.ext ?_⟩
    have hΦl : Φ ⟨(l : G), Subgroup.mem_inf.mpr ⟨l.2, hlcent⟩⟩ = φ l :=
      congrArg (fun q : ↥L => φ q) (Subtype.ext rfl)
    change ((Φ ⟨(l : G), Subgroup.mem_inf.mpr ⟨l.2, hlcent⟩⟩ : omegaGroup hQ) : OGroup Q) =
      g.val
    rw [hΦl]
    exact hlco
  refine ⟨MulEquiv.ofBijective ψ₀ ⟨hψ₀inj, hψ₀surj⟩, ?_⟩
  intro y
  rfl

end CFSG.OddStandard.SmallF3.Omega

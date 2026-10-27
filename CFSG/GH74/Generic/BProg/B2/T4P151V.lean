module

public import CFSG.GH74.Generic.BProg.B2.T4P151P
public import CFSG.GH74.Generic.BProg.B2.PumpupTableProved

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.P151V

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup
open scoped commutatorElement

section Inn

variable {H₀ : Type} [Group H₀]

theorem inn_normal : ((MulAut.conj : H₀ →* MulAut H₀).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨h, rfl⟩ := hn
  refine ⟨g h, ?_⟩
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem eq_one_of_comm_inn (hinj : Function.Injective (MulAut.conj : H₀ →* MulAut H₀)) (n : MulAut H₀)
    (hn : ∀ h ∈ (MulAut.conj : H₀ →* MulAut H₀).range, n * h = h * n) : n = 1 := by
  ext x
  have h1 := hn (MulAut.conj x) ⟨x, rfl⟩
  have h2 : MulAut.conj (n x) = MulAut.conj x := by
    ext y
    have := congrArg (fun φ : MulAut H₀ => φ (n⁻¹ y)) h1
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self] at this
    rw [MulAut.conj_apply, MulAut.conj_apply, this]
  exact hinj h2

end Inn

section Induced

variable {X : Type} [Group X] {L : Subgroup X} {σ : X}

@[expose] noncomputable def conjL (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) : ↥L ≃* ↥L :=
  ((MulAut.conj σ).subgroupMap L).trans (MulEquiv.subgroupCongr hLσ)

theorem conjL_apply (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) (l : ↥L) :
    ((conjL hLσ l : ↥L) : X) = σ * l * σ⁻¹ := rfl

@[expose] noncomputable def tau (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) : MulAut (↥L ⧸ center ↥L) :=
  QuotientGroup.congr (center ↥L) (center ↥L) (conjL hLσ) (Subgroup.map_center_eq (conjL hLσ))

theorem tau_mk (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) (l : ↥L) :
    tau hLσ (QuotientGroup.mk l) = QuotientGroup.mk (conjL hLσ l) :=
  QuotientGroup.congr_mk _ _ _ _ l

theorem tau_sq (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) (hσσ : σ * σ = 1) : tau hLσ * tau hLσ = 1 := by
  ext y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAut.mul_apply, tau_mk, tau_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [conjL_apply, conjL_apply]
  calc σ * (σ * (l : X) * σ⁻¹) * σ⁻¹ = (σ * σ) * l * (σ * σ)⁻¹ := by group
    _ = l := by rw [hσσ]; group

theorem tau_ne_one (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) (hperf : ⁅L, L⁆ = L)
    (hnt : ∃ l ∈ L, l * σ ≠ σ * l) : tau hLσ ≠ 1 := by
  intro h1
  obtain ⟨l₀, hl₀, hne⟩ := hnt
  have hz : ∀ l : ↥L, (l : ↥L)⁻¹ * conjL hLσ l ∈ center ↥L := by
    intro l
    have h2 : tau hLσ (QuotientGroup.mk l) = QuotientGroup.mk l := by rw [h1, MulAut.one_apply]
    rw [tau_mk] at h2
    exact QuotientGroup.eq.1 h2.symm
  have hcomm : ⁅L, L⁆ ≤ centralizer ({σ} : Set X) := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    set za := (⟨a, ha⟩ : ↥L)⁻¹ * conjL hLσ ⟨a, ha⟩ with hza
    set zb := (⟨b, hb⟩ : ↥L)⁻¹ * conjL hLσ ⟨b, hb⟩ with hzb
    have hca : conjL hLσ ⟨a, ha⟩ = ⟨a, ha⟩ * za := by rw [hza]; group
    have hcb : conjL hLσ ⟨b, hb⟩ = ⟨b, hb⟩ * zb := by rw [hzb]; group
    have hzaZ := hz ⟨a, ha⟩
    have hzbZ := hz ⟨b, hb⟩
    have hkey : conjL hLσ ⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆ = ⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆ := by
      rw [map_commutatorElement, hca, hcb]
      exact CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_mul_of_commute
        (Subgroup.mem_center_iff.1 hzaZ _).symm (Subgroup.mem_center_iff.1 hzaZ _).symm
        (Subgroup.mem_center_iff.1 hzbZ _).symm
    have hkey' : σ * ⁅a, b⁆ * σ⁻¹ = ⁅a, b⁆ := congrArg Subtype.val hkey
    calc ⁅a, b⁆ * σ = (σ * ⁅a, b⁆ * σ⁻¹) * σ := by rw [hkey']
      _ = σ * ⁅a, b⁆ := by group
  rw [hperf] at hcomm
  exact hne (Subgroup.mem_centralizer_singleton_iff.1 (hcomm hl₀))

theorem orderOf_tau (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) (hσσ : σ * σ = 1) (hperf : ⁅L, L⁆ = L)
    (hnt : ∃ l ∈ L, l * σ ≠ σ * l) : orderOf (tau hLσ) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact tau_sq hLσ hσσ) (tau_ne_one hLσ hperf hnt)

end Induced

section Fix

variable {X : Type} [Group X] {L : Subgroup X} {σ : X}

@[expose] noncomputable def fixTau (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) : Subgroup (↥L ⧸ center ↥L) :=
  (tau hLσ).toMonoidHom.eqLocus (MonoidHom.id _)

theorem mem_fixTau {hLσ : L.map (MulAut.conj σ).toMonoidHom = L} {y : ↥L ⧸ center ↥L} :
    y ∈ fixTau hLσ ↔ tau hLσ y = y := Iff.rfl

theorem map_conj_fixTau (hLσ : L.map (MulAut.conj σ).toMonoidHom = L)
    (hinj : Function.Injective (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L))) :
    (fixTau hLσ).map MulAut.conj =
      (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).range ⊓
        centralizer ({tau hLσ} : Set (MulAut (↥L ⧸ center ↥L))) := by
  have key : ∀ y : ↥L ⧸ center ↥L, tau hLσ * MulAut.conj y * (tau hLσ)⁻¹ = MulAut.conj (tau hLσ y) := by
    intro y
    ext z
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  ext φ
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := key y
    rw [mem_fixTau.1 hy] at h1
    calc MulAut.conj y * tau hLσ = tau hLσ * MulAut.conj y * (tau hLσ)⁻¹ * tau hLσ := by rw [h1]
      _ = tau hLσ * MulAut.conj y := by group
  · rintro hφ
    obtain ⟨⟨y, rfl⟩, hc⟩ := Subgroup.mem_inf.1 hφ
    refine ⟨y, mem_fixTau.2 (hinj ?_), rfl⟩
    rw [← key y]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hc
    calc tau hLσ * MulAut.conj y * (tau hLσ)⁻¹ = MulAut.conj y * tau hLσ * (tau hLσ)⁻¹ := by rw [h1]
      _ = MulAut.conj y := by group

theorem map_le_fixTau (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) {J : Subgroup X}
    (hJσ : J ≤ centralizer ({σ} : Set X)) :
    (J.subgroupOf L).map (QuotientGroup.mk' (center ↥L)) ≤ fixTau hLσ := by
  rintro _ ⟨j, hj, rfl⟩
  rw [mem_fixTau, QuotientGroup.mk'_apply, tau_mk]
  congr 1
  apply Subtype.ext
  rw [conjL_apply]
  have hjσ : (j : X) * σ = σ * j := Subgroup.mem_centralizer_singleton_iff.1 (hJσ (Subgroup.mem_subgroupOf.1 hj))
  calc σ * (j : X) * σ⁻¹ = (j * σ) * σ⁻¹ := by rw [hjσ]
    _ = j := by group

theorem conj_mem_imgC (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) {h c : ↥L}
    (hh : tau hLσ (QuotientGroup.mk h) = QuotientGroup.mk h) (hc : (c : X) * σ = σ * c) :
    ((h * c * h⁻¹ : ↥L) : X) * σ = σ * (h * c * h⁻¹ : ↥L) := by
  rw [tau_mk] at hh
  have hz : h⁻¹ * conjL hLσ h ∈ center ↥L := QuotientGroup.eq.1 hh.symm
  set z := h⁻¹ * conjL hLσ h with hzdef
  have hch : conjL hLσ h = h * z := by rw [hzdef]; group
  have hch' : σ * (h : X) * σ⁻¹ = h * z := by rw [← conjL_apply hLσ h, hch]; rfl
  have hzc : ∀ g : ↥L, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  have hcσ : σ * (c : X) * σ⁻¹ = c := by
    calc σ * (c : X) * σ⁻¹ = (c * σ) * σ⁻¹ := by rw [hc]
      _ = c := by group
  have h1 : σ * ((h * c * h⁻¹ : ↥L) : X) * σ⁻¹ = (h * c * h⁻¹ : ↥L) := by
    have e1 : σ * ((h * c * h⁻¹ : ↥L) : X) * σ⁻¹ =
        (σ * (h : X) * σ⁻¹) * (σ * c * σ⁻¹) * (σ * (h : X) * σ⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1, hch', hcσ]
    have e2 : ((h : X) * z) * c * ((h : X) * z)⁻¹ = ((h * z * c * (h * z)⁻¹ : ↥L) : X) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2]
    congr 1
    calc h * z * c * (h * z)⁻¹ = h * (z * c) * z⁻¹ * h⁻¹ := by group
      _ = h * (c * z) * z⁻¹ * h⁻¹ := by rw [hzc c]
      _ = h * c * h⁻¹ := by group
  calc ((h * c * h⁻¹ : ↥L) : X) * σ = (σ * ((h * c * h⁻¹ : ↥L) : X) * σ⁻¹) * σ := by rw [h1]
    _ = σ * ((h * c * h⁻¹ : ↥L) : X) := by group

theorem isCompIn_fixTau (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) {J : Subgroup X}
    (hJ : IsCompIn (centralizer ({σ} : Set X)) J) (hJL : J ≤ L) :
    IsCompIn (fixTau hLσ) ((J.subgroupOf L).map (QuotientGroup.mk' (center ↥L))) := by
  classical
  set π := QuotientGroup.mk' (center ↥L) with hπ
  set Jb := (J.subgroupOf L).map π with hJbdef
  have hJb : Jb ≤ fixTau hLσ := map_le_fixTau hLσ hJ.1
  have hJq : IsQuasisimple ↥J := Prop31.isQuasisimple_of_isCompIn hJ
  set ρ : ↥J →* ↥Jb := (π.comp (Subgroup.inclusion hJL)).codRestrict Jb
    (fun j => ⟨Subgroup.inclusion hJL j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩) with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩
    exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩
  have hρk : ρ.ker ≤ center ↥J := by
    intro j hj
    have h1 : π (Subgroup.inclusion hJL j) = 1 := congrArg Subtype.val hj
    have h2 : Subgroup.inclusion hJL j ∈ center ↥L := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro g
    have h3 := Subgroup.mem_center_iff.1 h2 (Subgroup.inclusion hJL g)
    have h4 : ((g * j : ↥J) : X) = ((j * g : ↥J) : X) := congrArg (fun y : ↥L => (y : X)) h3
    exact Subtype.ext h4
  have hJbq : IsQuasisimple ↥Jb := CFSG.LocalCores.isQuasisimple_of_surjective hJq ρ hρs hρk
  refine ⟨hJb, CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJb).symm hJbq, ?_⟩
  set W : Subgroup X := L ⊓ centralizer ({σ} : Set X) with hW
  have hJW : (J.subgroupOf W).IsSubnormal :=
    TwoThin.isSubnormal_inf_subgroupOf hJ.2.2 inf_le_right
  have hfW : ∀ w : ↥W, π ⟨(w : X), (Subgroup.mem_inf.1 w.2).1⟩ ∈ fixTau hLσ := by
    intro w
    rw [mem_fixTau, hπ, QuotientGroup.mk'_apply, tau_mk]
    congr 1
    apply Subtype.ext
    rw [conjL_apply]
    have hwσ : (w : X) * σ = σ * w := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 w.2).2
    calc σ * (w : X) * σ⁻¹ = (w * σ) * σ⁻¹ := by rw [hwσ]
      _ = w := by group
  set f : ↥W →* ↥(fixTau hLσ) :=
    { toFun := fun w => ⟨π ⟨(w : X), (Subgroup.mem_inf.1 w.2).1⟩, hfW w⟩
      map_one' := by
        apply Subtype.ext
        show π ⟨1, _⟩ = 1
        exact map_one π
      map_mul' := fun w w' => by
        apply Subtype.ext
        show π ⟨(w : X) * w', _⟩ = π ⟨w, _⟩ * π ⟨w', _⟩
        rw [← map_mul]
        rfl } with hf
  set R : Subgroup ↥(fixTau hLσ) := f.range with hR
  have hRn : R.Normal := by
    refine ⟨fun r hr y => ?_⟩
    obtain ⟨w, rfl⟩ := hr
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (y : ↥L ⧸ center ↥L)
    have hhy : tau hLσ (QuotientGroup.mk h) = QuotientGroup.mk h := by rw [hh]; exact y.2
    set c : ↥L := ⟨(w : X), (Subgroup.mem_inf.1 w.2).1⟩ with hc
    have hcσ : (c : X) * σ = σ * c := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 w.2).2
    have hconj := conj_mem_imgC hLσ hhy hcσ
    refine ⟨⟨((h * c * h⁻¹ : ↥L) : X), Subgroup.mem_inf.2 ⟨(h * c * h⁻¹ : ↥L).2,
      Subgroup.mem_centralizer_singleton_iff.2 hconj⟩⟩, ?_⟩
    apply Subtype.ext
    show π ⟨((h * c * h⁻¹ : ↥L) : X), _⟩ = ((y * f w * y⁻¹ : ↥(fixTau hLσ)) : ↥L ⧸ center ↥L)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hh]
    show π (h * c * h⁻¹) = π h * π c * (π h)⁻¹
    rw [map_mul, map_mul, map_inv]
  have h1 : ((J.subgroupOf W).map f.rangeRestrict).IsSubnormal := hJW.map f.rangeRestrict_surjective
  have h2 := h1.trans' hRn.isSubnormal
  have heq : ((J.subgroupOf W).map f.rangeRestrict).map R.subtype = Jb.subgroupOf (fixTau hLσ) := by
    ext y
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine Subgroup.mem_subgroupOf.2 ⟨⟨(w : X), (Subgroup.mem_inf.1 w.2).1⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hw), rfl⟩
    · intro hy
      obtain ⟨l, hl, hly⟩ := Subgroup.mem_subgroupOf.1 hy
      have hlJ : (l : X) ∈ J := Subgroup.mem_subgroupOf.1 hl
      have hlW : (l : X) ∈ W := Subgroup.mem_inf.2 ⟨l.2, hJ.1 hlJ⟩
      refine ⟨f.rangeRestrict ⟨l, hlW⟩, ⟨⟨l, hlW⟩, Subgroup.mem_subgroupOf.2 hlJ, rfl⟩, ?_⟩
      apply Subtype.ext
      exact hly
  rw [heq] at h2
  exact h2

end Fix

section Shape

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {σ : X}

theorem puTarget_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : PuTarget A) : PuTarget B := by
  rcases h with ⟨p, f, hp, hp2, hf, ⟨h4, hm⟩ | ⟨h4, hm⟩⟩ | ⟨p, f, hp, hp2, hf, h3, ⟨h8, hm⟩ | ⟨h8, hm⟩⟩ |
      ⟨p, f, hp, hp2, hf, hm⟩ | ⟨f, hf, hm⟩
  · exact Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩
  · exact Or.inl ⟨p, f, hp, hp2, hf, Or.inr ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h3, Or.inl ⟨h8, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩)
  · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h3, Or.inr ⟨h8, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨f, hf, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩))

omit [Finite X] in
theorem center_trivial_of_component (hL : IsComponent L) :
    ∀ z : ↥L ⧸ center ↥L, (∀ g : ↥L ⧸ center ↥L, g * z = z * g) → z = 1 := by
  have hsimple : IsSimpleGroup (↥L ⧸ center ↥L) := hL.1.2.1
  intro z hz
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥L ⧸ center ↥L)) with hb | ht
  · have : z ∈ center (↥L ⧸ center ↥L) := Subgroup.mem_center_iff.2 hz
    rw [hb] at this
    exact Subgroup.mem_bot.1 this
  · exfalso
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    apply hab
    have : b ∈ center (↥L ⧸ center ↥L) := ht ▸ Subgroup.mem_top b
    exact (Subgroup.mem_center_iff.1 this a)

omit [Finite X] in
theorem jbar_facts {J : Subgroup X} (hJq : IsQuasisimple ↥J) (hJL : J ≤ L) :
    Nonempty ((↥J ⧸ center ↥J) ≃* (↥((J.subgroupOf L).map (QuotientGroup.mk' (center ↥L))) ⧸
      center ↥((J.subgroupOf L).map (QuotientGroup.mk' (center ↥L))))) ∧
    Nat.card ↥(center ↥((J.subgroupOf L).map (QuotientGroup.mk' (center ↥L)))) ∣ Nat.card ↥(center ↥J) := by
  set π := QuotientGroup.mk' (center ↥L) with hπ
  set Jb : Subgroup (↥L ⧸ center ↥L) := (J.subgroupOf L).map π with hJbdef
  set ρ : ↥J →* ↥Jb := (π.comp (Subgroup.inclusion hJL)).codRestrict Jb
    (fun j => ⟨Subgroup.inclusion hJL j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩) with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩
    exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩
  have hρk : ρ.ker ≤ center ↥J := by
    intro j hj
    have h1 : π (Subgroup.inclusion hJL j) = 1 := congrArg Subtype.val hj
    have h2 : Subgroup.inclusion hJL j ∈ center ↥L := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro g
    have h3 := Subgroup.mem_center_iff.1 h2 (Subgroup.inclusion hJL g)
    have h4 : ((g * j : ↥J) : X) = ((j * g : ↥J) : X) := congrArg (fun y : ↥L => (y : X)) h3
    exact Subtype.ext h4
  refine ⟨CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hJq ρ hρs hρk, ?_⟩
  have hcen : center ↥Jb = (center ↥J).map ρ := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hJq.1 ρ hρs hρk,
      Subgroup.map_comap_eq_self_of_surjective hρs]
  rw [hcen]
  exact Subgroup.card_map_dvd _ _

theorem shapeInCent_of_vert (hL : IsComponent L) (hσσ : σ * σ = 1)
    (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) (hnt : ∃ l ∈ L, l * σ ≠ σ * l)
    {J : Subgroup X} (hJ : IsCompIn (centralizer ({σ} : Set X)) J)
    (hJL : J ≤ L) (hJT : QShape3 (↥J ⧸ center ↥J)) (hJZ : Odd (Nat.card ↥(center ↥J))) :
    ShapeInCent (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).range (tau hLσ)
      (((J.subgroupOf L).map (QuotientGroup.mk' (center ↥L))).map MulAut.conj) := by
  classical
  set H₀ := ↥L ⧸ center ↥L with hH₀
  have hsimple : IsSimpleGroup H₀ := hL.1.2.1
  have hinj : Function.Injective (MulAut.conj : H₀ →* MulAut H₀) :=
    GenLocBasic.conj_injective_of_center_trivial (center_trivial_of_component hL)
  set H : Subgroup (MulAut H₀) := (MulAut.conj : H₀ →* MulAut H₀).range with hH
  set eH : H₀ ≃* ↥H := MonoidHom.ofInjective hinj with heH
  set π := QuotientGroup.mk' (center ↥L) with hπ
  set Jb : Subgroup H₀ := (J.subgroupOf L).map π with hJbdef
  set L' : Subgroup (MulAut H₀) := Jb.map MulAut.conj with hL'
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  have hJc := isCompIn_fixTau hLσ hJ hJL
  have hJq : IsQuasisimple ↥J := Prop31.isQuasisimple_of_isCompIn hJ
  obtain ⟨⟨eJ⟩, hdvd⟩ := jbar_facts hJq hJL
  set eL : ↥Jb ≃* ↥L' := Jb.equivMapOfInjective _ hinj with heL
  have hshape : ∃ Z : Subgroup ↥L', Z ≤ center ↥L' ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      QShapeNS (↥L' ⧸ Z) := by
    refine ⟨center ↥L', le_rfl, ?_, inferInstance, ?_⟩
    · have h2 : Nat.card ↥(center ↥L') = Nat.card ↥(center ↥Jb) := by
        rw [← Subgroup.map_center_eq eL]
        exact Nat.card_congr ((center ↥Jb).equivMapOfInjective _ eL.injective).toEquiv.symm
      rw [h2]
      exact Odd.of_dvd_nat hJZ hdvd
    · exact Or.inr (Or.inl (T4ElimAssembly.qShape3_of_equiv
        (eJ.trans (CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr eL)) hJT))
  have hs : ShapeInCent H (tau hLσ) L' := by
    refine ⟨inn_normal, (MulEquiv.isSimpleGroup_congr eH).1 hsimple, eq_one_of_comm_inn hinj,
      orderOf_tau hLσ hσσ hperf hnt, ?_, hshape⟩
    rw [← map_conj_fixTau hLσ hinj]
    exact B3aG.isCompIn_map_of_injective hinj hJc
  exact hs

end Shape

section Table

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {σ : X}


theorem puTarget_of_vert (hL : IsComponent L) (hσσ : σ * σ = 1)
    (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) (hnt : ∃ l ∈ L, l * σ ≠ σ * l)
    (hGH : GHList (↥L ⧸ center ↥L)) {J : Subgroup X} (hJ : IsCompIn (centralizer ({σ} : Set X)) J)
    (hJL : J ≤ L) (hJT : QShape3 (↥J ⧸ center ↥J)) (hJZ : Odd (Nat.card ↥(center ↥J))) :
    PuTarget (↥L ⧸ center ↥L) := by
  have hZ : ∀ z : ↥L ⧸ center ↥L, (∀ g : ↥L ⧸ center ↥L, g * z = z * g) → z = 1 :=
    center_trivial_of_component hL
  have hinj : Function.Injective (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)) :=
    GenLocBasic.conj_injective_of_center_trivial hZ
  exact puTarget_of_mulEquiv (MonoidHom.ofInjective hinj).symm
    (PumpupOutOrders.pumpupTableU_proved _ _ (tau hLσ) _
      (shapeInCent_of_vert hL hσσ hLσ hnt hJ hJL hJT hJZ) (GHList.of_mulEquiv (MonoidHom.ofInjective hinj) hGH))

end Table

section Gen

open CFSG.RankThree.PerfectCover

variable {L : Type} [Group L] [Finite L]

theorem sup_centralizer_eq_top_of_genInner (hq : IsQuasisimple L) (hG : GenLocL5Out.GenInner (L ⧸ center L))
    (hZ : Odd (Nat.card ↥(center L))) {u₁ u₂ : L} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1)
    (h₁₂ : u₁ * u₂ = u₂ * u₁) (h₁1 : u₁ ≠ 1) (h₂1 : u₂ ≠ 1) (hne : u₁ ≠ u₂) :
    centralizer ({u₁} : Set L) ⊔ centralizer ({u₂} : Set L) ⊔ centralizer ({u₁ * u₂} : Set L) = ⊤ := by
  classical
  set E : Subgroup L := zpowers u₁ ⊔ zpowers u₂ with hEdef
  have hc₁₂ : ∀ h ∈ zpowers u₁, h * u₂ = u₂ * h := by
    intro h hh
    obtain h' | h' := P151G.mem_zpowers_invol h₁ hh
    · rw [h']; simp
    · rw [h']; exact h₁₂
  have hEel : CFSG.IsElementaryAbelian 2 ↥E :=
    B3.S3Sec29H.isElementaryAbelian_sup_zpowers (P151G.isElementaryAbelian_zpowers_invol h₁) h₂ hc₁₂
  have hE4 : Nat.card ↥E = 4 := P151G.card_four h₁ h₂ h₁₂ h₁1 h₂1 hne
  have hrank : pRank 2 ↥E = 2 := by
    have h1 := WeakSigGen.card_eq_two_pow_pRank hEel
    rw [hE4] at h1
    have h2 : 2 ^ pRank 2 ↥E = 2 ^ 2 := by rw [← h1]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  set α : ↥E →* MulAut L := ShapeGenS13.conjOn E with hα
  set ρ : ↥E →* L ⧸ center L := (QuotientGroup.mk' (center L)).comp E.subtype with hρ
  set α' : ↥E →* MulAut (L ⧸ center L) := (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).comp ρ
    with hα'
  have hcompat : ∀ (a : ↥E) (x : L), α' a (QuotientGroup.mk x) = QuotientGroup.mk (α a x) := by
    intro a x
    simp only [hα', hρ, hα, MonoidHom.comp_apply, MulAut.conj_apply, ShapeGenS13.conjOn_apply]
    rfl
  have hγ' : gammaAct α' = ⊤ :=
    hG ↥E α' ⟨hEel, Or.inl hrank⟩ (by rintro _ ⟨b, rfl⟩; exact ⟨ρ b, rfl⟩)
  have hperf : commutator L = ⊤ := by
    have : Group.IsPerfect L := hq.1
    exact Group.IsPerfect.commutator_eq_top
  have hγ : gammaAct α = ⊤ :=
    gammaAct_eq_top_of_quotient hEel hperf (center L) le_rfl hZ α α' hcompat hγ'
  have hnc : ∀ E' : Subgroup ↥E, pRank 2 ↥E - 1 ≤ pRank 2 ↥E' → ∃ b ∈ E', (b : L) ∉ center L := by
    intro E' hE'
    obtain ⟨b, hbE', hb1⟩ := ShapeGenS13.exists_ne_one_of_one_le_pRank (E := E') (by omega)
    refine ⟨b, hbE', P151P.not_mem_center_of_invol hZ ?_ ?_⟩
    · exact congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hEel b)
    · intro h
      exact hb1 (Subtype.ext h)
  have hsup := ShapeGenS13.shapeGen_of_gammaAct hnc hγ
  refine eq_top_iff.2 (hsup.symm.le.trans ?_)
  refine iSup₂_le fun b hb => ?_
  obtain ⟨hbE, hbZ⟩ := hb
  rcases P151G.mem_four h₁ h₂ h₁₂ hbE with rfl | rfl | rfl | rfl
  · exact absurd (Subgroup.one_mem _) hbZ
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem odd_hopfMultiplier_of_puL5 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] (h : PuL5 Y) : Odd (Nat.card (hopfMultiplier Y)) := by
  obtain ⟨p, f, hp, hp2, hf, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := h
  · have hm' : CFSG.Models.LieModel Y .PSL 5 p f := models_of_blueprint_of_ne_zero (by norm_num) hm
    rw [card_hopfMultiplier_of_griess hGA hm']
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 5 p f = (Nat.gcd 5 (p ^ f - 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 5 p f = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    rw [hgen, hexc]
    simpa using odd_gcd_of_odd_left (b := p ^ f - 1) (by decide : Odd 5)
  · have hm' : CFSG.Models.LieModel Y .PSU 5 p f := models_of_blueprint_of_ne_zero (by norm_num) hm
    rw [card_hopfMultiplier_of_griess hGA hm']
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 5 p f = (Nat.gcd 5 (p ^ f + 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 5 p f = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    rw [hgen, hexc]
    simpa using odd_gcd_of_odd_left (b := p ^ f + 1) (by decide : Odd 5)

theorem odd_hopfMultiplier_of_puL3sq (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] (h : PuL3sq Y) : Odd (Nat.card (hopfMultiplier Y)) := by
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := h
  have hm' : CFSG.Models.LieModel Y .PSL 3 p (2 * f) := models_of_blueprint_of_ne_zero (by norm_num) hm
  rw [S3.card_hopfMultiplier_psl_three hGA hp2 hm']
  exact odd_gcd_of_odd_left (by decide)

theorem odd_card_center_of_odd_hopf (hq : IsQuasisimple L) (hM : Odd (Nat.card (hopfMultiplier (L ⧸ center L)))) :
    Odd (Nat.card ↥(center L)) := by
  have hperf : Group.IsPerfect L := hq.1
  have hd := card_ker_dvd_hopfMultiplier hperf (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  rw [QuotientGroup.ker_mk'] at hd
  exact Odd.of_dvd_nat hM hd

end Gen

@[expose] def VertGenFor (P : ∀ (Y : Type) [Group Y], Prop) (Q : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → pPrimeCore 2 X = ⊥ →
    ∀ σ : X, orderOf σ = 2 → ∀ L : Subgroup X, IsComponent L → GHList (↥L ⧸ center ↥L) →
      P (↥L ⧸ center ↥L) → L.map (MulAut.conj σ).toMonoidHom = L → (∃ l ∈ L, l * σ ≠ σ * l) →
    ∀ J : Subgroup X, IsCompIn (centralizer ({σ} : Set X)) J → J ≤ L →
      Q (↥J ⧸ center ↥J) → (∀ z ∈ J, (∀ l ∈ J, z * l = l * z) → z * z = 1 → z = 1) →
    ∀ e₁ e₂ : X, e₁ ∈ J → e₂ ∈ J → e₁ * e₁ = 1 → e₂ * e₂ = 1 → e₁ * e₂ = e₂ * e₁ →
      e₁ ≠ 1 → e₂ ≠ 1 → e₁ ≠ e₂ →
      L ≤ (L ⊓ centralizer ({e₁} : Set X)) ⊔ (L ⊓ centralizer ({e₂} : Set X)) ⊔
        (L ⊓ centralizer ({e₁ * e₂} : Set X))

@[expose] def VertL4 : Prop := VertGenFor (fun Y _ => PuL4 Y) (fun Y _ => QShape3 Y)

@[expose] def VertG2 : Prop := VertGenFor (fun Y _ => PuG2 Y) (fun Y _ => QShape3 Y)

@[expose] def VertQ3 : Prop :=
  VertGenFor (fun _ _ => True) (fun Y _ => CFSG.Blueprint.LieModel Y .PSL 3 3 1)

section Assembly


theorem pumpGenVert3_of (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hL4 : VertL4) (hG2 : VertG2) (hQ3 : VertQ3) : P151P.PumpGenVert3 := by
  intro X _ _ hG4 hO σ hσ L hL hGH hLσ hnt J hJ hJL hJT hJZ e₁ e₂ he₁ he₂ h₁ h₂ h₁₂ h₁1 h₂1 hne
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hgenL : ∀ (P : ∀ (Y : Type) [Group Y], Prop), (∀ (Y : Type) [Group Y], P Y → GenLocL5Out.GenInner Y) →
      (∀ (Y : Type) [Group Y], P Y → Odd (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y))) →
      P (↥L ⧸ center ↥L) →
      L ≤ (L ⊓ centralizer ({e₁} : Set X)) ⊔ (L ⊓ centralizer ({e₂} : Set X)) ⊔
        (L ⊓ centralizer ({e₁ * e₂} : Set X)) := by
    intro P hPG hPM hP
    have hZ := odd_card_center_of_odd_hopf hL.1 (hPM _ hP)
    have htop : centralizer ({(⟨e₁, hJL he₁⟩ : ↥L)} : Set ↥L) ⊔ centralizer ({(⟨e₂, hJL he₂⟩ : ↥L)} : Set ↥L) ⊔
        centralizer ({(⟨e₁, hJL he₁⟩ : ↥L) * ⟨e₂, hJL he₂⟩} : Set ↥L) = ⊤ :=
      sup_centralizer_eq_top_of_genInner hL.1 (hPG _ hP) hZ (Subtype.ext h₁) (Subtype.ext h₂) (Subtype.ext h₁₂)
        (fun h => h₁1 (congrArg Subtype.val h)) (fun h => h₂1 (congrArg Subtype.val h))
        (fun h => hne (congrArg Subtype.val h))
    have hle := P151P.le_sup_of_top htop
    exact hle
  obtain ⟨p, f, hp, hp2, hm4⟩ := hJT
  have hm : CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 3 p f ∨
      CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSU 3 p f := by
    rcases hm4 with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  by_cases hq : 3 < p ^ f
  · have hJT' : QShape3 (↥J ⧸ center ↥J) := ⟨p, f, hp, hp2, hq, hm⟩
    have hJZo : Odd (Nat.card ↥(center ↥J)) := P151P.odd_card_center_of_noInvol hJZ
    rcases puTarget_of_vert hL hσσ hLσ hnt hGH hJ hJL hJT' hJZo with h5 | h4 | h3 | h2
    · exact hgenL (fun Y _ => PuL5 Y) (fun Y _ h => GenLocL5Out.genInner_of_puL5 h)
        (fun Y _ h => odd_hopfMultiplier_of_puL5 hGA h) h5
    · exact hL4 X hG4 hO σ hσ L hL hGH h4 hLσ hnt J hJ hJL hJT' hJZ e₁ e₂ he₁ he₂ h₁ h₂ h₁₂ h₁1 h₂1 hne
    · refine hgenL (fun Y _ => PuL3sq Y) (fun Y _ h => ?_) (fun Y _ h => odd_hopfMultiplier_of_puL3sq hGA h) h3
      obtain ⟨p', f', hp', hp2', -, hm'⟩ := h
      exact P151P.genInner_of_isL3Odd ⟨p', 2 * f', hp', hp2', Or.inl hm'⟩
    · exact hG2 X hG4 hO σ hσ L hL hGH h2 hLσ hnt J hJ hJL hJT' hJZ e₁ e₂ he₁ he₂ h₁ h₂ h₁₂ h₁1 h₂1 hne
  ·
    have hf1 : 1 ≤ f := by
      rcases hm with hm | hm
      · exact (GenLocL5Out.stated_PSL hm).1.2.1
      · exact (GenLocL5Out.stated_PSU hm).1.2.1
    have h3p : 3 ≤ p := by
      have := hp.two_le
      have : p ≠ 2 := hp2
      omega
    have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hp3 : p = 3 := by omega
    subst hp3
    have hf : f = 1 := by
      by_contra hf
      have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hf
    have hL3 : CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 3 3 1 := by
      rcases hm4 with ⟨-, h⟩ | ⟨h4, -⟩
      · exact h
      · exact absurd h4 (by norm_num)
    exact hQ3 X hG4 hO σ hσ L hL hGH trivial hLσ hnt J hJ hJL hL3 hJZ e₁ e₂ he₁ he₂ h₁ h₂ h₁₂ h₁1 h₂1 hne

end Assembly

end CFSG.GH74.Generic.BProg.B2.T4.P151V

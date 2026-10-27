module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

section Commutator

variable {V : Type*} [CommGroup V]

theorem commV_mono {H L : Subgroup (MulAut V)} (h : L ≤ H) : commV L ≤ commV H :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hv⟩ => ⟨x, h hx, v, hv⟩

theorem apply_mul_inv_mem_commV {L : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ L) (v : V) :
    x v * v⁻¹ ∈ commV L :=
  Subgroup.subset_closure ⟨x, hx, v, rfl⟩

theorem apply_mem_commV {L : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ L) {u : V}
    (hu : u ∈ commV L) : x u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem hx hu

theorem apply_mem_commV_of_mem_normalizer {L : Subgroup (MulAut V)} {h : MulAut V}
    (hh : h ∈ Subgroup.normalizer (L : Set (MulAut V))) {u : V} (hu : u ∈ commV L) :
    h u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hh hu

theorem apply_mem_fixV_of_mem_normalizer {L : Subgroup (MulAut V)} {h : MulAut V}
    (hh : h ∈ Subgroup.normalizer (L : Set (MulAut V))) {u : V} (hu : u ∈ fixV L) :
    h u ∈ fixV L :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hh hu

@[expose] def commVRestrict {L : Subgroup (MulAut V)} {h : MulAut V}
    (hh : h ∈ Subgroup.normalizer (L : Set (MulAut V))) : ↥(commV L) →* ↥(commV L) :=
  (h.toMonoidHom.comp (commV L).subtype).codRestrict (commV L) fun u =>
    apply_mem_commV_of_mem_normalizer hh u.2

theorem coe_commVRestrict {L : Subgroup (MulAut V)} {h : MulAut V}
    (hh : h ∈ Subgroup.normalizer (L : Set (MulAut V))) (u : ↥(commV L)) :
    ((commVRestrict hh u : ↥(commV L)) : V) = h u := rfl

end Commutator

theorem isAltNaturalSection_commV_of_le {V : Type} [CommGroup V] {H L : Subgroup (MulAut V)}
    (hLH : L ≤ H) {n : ℕ} (hn : 4 ≤ n) (h : IsAltNaturalSection L (commV H) n) :
    IsAltNaturalSection L (commV L) n := by
  obtain ⟨α, hα, π, hπ, hker, heq⟩ := h
  set ι : ↥(commV L) →* ↥(commV H) := Subgroup.inclusion (commV_mono hLH) with hι
  refine ⟨α, hα, π.comp ι, ?_, ?_, fun l u v huv x hx => heq l (ι u) (ι v) huv x hx⟩
  · let U : AddSubgroup (altHeart n) :=
      { carrier := {a | ∃ u : ↥(commV L), Multiplicative.toAdd (π (ι u)) = a}
        add_mem' := by
          rintro _ _ ⟨u, rfl⟩ ⟨w, rfl⟩
          exact ⟨u * w, by rw [map_mul, map_mul, toAdd_mul]⟩
        zero_mem' := ⟨1, by rw [map_one, map_one, toAdd_one]⟩
        neg_mem' := by
          rintro _ ⟨u, rfl⟩
          exact ⟨u⁻¹, by rw [map_inv, map_inv, toAdd_inv]⟩ }
    have hUinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ x : evenWeight n, (x : altHeart n) ∈ U →
        (evenWeightPerm σ x : altHeart n) ∈ U := by
      rintro σ hσ x ⟨u, hu⟩
      obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
      refine ⟨⟨(l : MulAut V) (u : V), apply_mem_commV l.2 u.2⟩, ?_⟩
      have := heq l (ι u) (ι ⟨(l : MulAut V) (u : V), apply_mem_commV l.2 u.2⟩) rfl x hu
      rw [hl] at this
      exact this
    rcases altHeart_irreducible hn U hUinv with hbot | htop
    · exfalso
      have hfix : ∀ x : evenWeight n, ∀ σ ∈ alternatingGroup (Fin n),
          (evenWeightPerm σ x : altHeart n) = (x : altHeart n) := by
        intro x σ hσ
        obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
        obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd (x : altHeart n))
        set w : ↥(commV H) := ⟨(l : MulAut V) (u : V), apply_mem_commV (hLH l.2) u.2⟩ with hw
        have hwx : Multiplicative.toAdd (π w) = (evenWeightPerm σ x : altHeart n) := by
          have := heq l u w rfl x (by rw [hu, toAdd_ofAdd])
          rw [hl] at this
          exact this
        have hc : ι ⟨(l : MulAut V) (u : V) * (u : V)⁻¹, apply_mul_inv_mem_commV l.2 (u : V)⟩ =
            w * u⁻¹ := rfl
        have h1 : Multiplicative.toAdd (π (ι ⟨(l : MulAut V) (u : V) * (u : V)⁻¹,
            apply_mul_inv_mem_commV l.2 (u : V)⟩)) ∈ U := ⟨_, rfl⟩
        rw [hbot, AddSubgroup.mem_bot, hc, map_mul, map_inv, toAdd_mul, toAdd_inv, hwx, hu,
          toAdd_ofAdd] at h1
        exact add_neg_eq_zero.1 h1
      obtain ⟨a, b, hab⟩ := altHeart_nontrivial (n := n) (by omega)
      obtain ⟨xa, rfl⟩ := QuotientAddGroup.mk_surjective a
      obtain ⟨xb, rfl⟩ := QuotientAddGroup.mk_surjective b
      rw [altHeart_fixed_eq_zero hn xa (fun σ hσ => hfix xa σ hσ),
        altHeart_fixed_eq_zero hn xb (fun σ hσ => hfix xb σ hσ)] at hab
      exact hab rfl
    · intro b
      obtain ⟨u, hu⟩ : Multiplicative.toAdd b ∈ U := htop ▸ AddSubgroup.mem_top _
      exact ⟨u, Multiplicative.toAdd.injective hu⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨u.2, h.2⟩, fun h => ⟨(ι u).2, h.2⟩⟩

@[expose] def autTransport {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    MulAut A →* MulAut B where
  toFun φ := (e.symm.trans φ).trans e
  map_one' := MulEquiv.ext fun b => e.apply_symm_apply b
  map_mul' φ ψ := by ext; simp [MulAut.mul_apply]

theorem autTransport_apply {A B : Type*} [Group A] [Group B] (e : A ≃* B) (φ : MulAut A) (b : B) :
    autTransport e φ b = e (φ (e.symm b)) := rfl

theorem exists_permRep_of_isAltNaturalSection {V : Type} [CommGroup V] [Finite V]
    {H L : Subgroup (MulAut V)} (hLF : L = quasithinGenFitting H) (hLH : L ≤ H) {n : ℕ}
    (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hiso : Nonempty (↥L ≃* alternatingGroup (Fin n)))
    (hnat : IsAltNaturalSection L (commV L) n) :
    ∃ (θ : ↥H →* Equiv.Perm (Fin n)) (π : ↥(commV L) →* Multiplicative (altHeart n)),
      Function.Surjective π ∧ π.ker = (commV L ⊓ fixV L).subgroupOf (commV L) ∧
      alternatingGroup (Fin n) ≤ (θ.comp (Subgroup.inclusion hLH)).range ∧
      (∀ (h : ↥H) (u v : ↥(commV L)), (v : V) = (h : MulAut V) (u : V) → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (x : altHeart n) →
        Multiplicative.toAdd (π v) = (evenWeightPerm (θ h) x : altHeart n)) ∧
      Function.Injective θ := by
  classical
  obtain ⟨eL⟩ := hiso
  obtain ⟨α, hα, π, hπ, hker, heq⟩ := hnat
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting H
  have hαi : Function.Injective α :=
    (Finite.injective_iff_surjective_of_equiv eL.toEquiv).2 hα
  set e : ↥L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective α ⟨hαi, hα⟩ with he
  set cH : ↥H →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hHN) with hcH
  have hcH_apply : ∀ (h : ↥H) (l : ↥L),
      ((cH h l : ↥L) : MulAut V) = (h : MulAut V) * l * (h : MulAut V)⁻¹ := fun _ _ => rfl
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  set cA : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ hb
    with hcA
  set θ : ↥H →* Perm (Fin n) := cA.symm.toMonoidHom.comp ((autTransport e).comp cH) with hθ
  have hcAθ : ∀ h : ↥H, cA (θ h) = autTransport e (cH h) := fun h => cA.apply_symm_apply _
  have hconj : ∀ (h : ↥H) (l : ↥L),
      (θ h : Perm (Fin n)) * (α l : Perm (Fin n)) * (θ h)⁻¹ = (α (cH h l) : Perm (Fin n)) := by
    intro h l
    have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin n)) =>
      ((φ (α l) : alternatingGroup (Fin n)) : Perm (Fin n))) (hcAθ h)
    rw [show cA (θ h) = MulAut.conjNormal (θ h) from rfl, MulAut.conjNormal_apply,
      autTransport_apply, show e.symm (α l) = l from e.symm_apply_apply l] at h1
    exact h1
  have hθL : ∀ l : ↥L, θ (Subgroup.inclusion hLH l) = (α l : Perm (Fin n)) := by
    intro l
    rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [show cA (α l : Perm (Fin n)) = MulAut.conjNormal (α l : Perm (Fin n)) from rfl,
      MulAut.conjNormal_apply, MonoidHom.comp_apply, autTransport_apply]
    have hl : cH (Subgroup.inclusion hLH l) (e.symm x) = l * e.symm x * l⁻¹ := Subtype.ext rfl
    rw [hl, map_mul, map_mul, map_inv, e.apply_symm_apply]
    rfl
  have hLact : ∀ (l : ↥L) (u : ↥(commV L)),
      Multiplicative.toAdd (π (commVRestrict (Subgroup.le_normalizer l.2) u)) =
        altAct (α l) (Multiplicative.toAdd (π u)) := by
    intro l u
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π u))
    rw [← hx, altAct_mk]
    exact heq l u _ rfl x hx.symm
  have hHact : ∀ (h : ↥H) (u : ↥(commV L)),
      Multiplicative.toAdd (π (commVRestrict (hHN h.2) u)) =
        altAct (θ h) (Multiplicative.toAdd (π u)) := by
    intro h
    set R := commVRestrict (hHN h.2) with hR
    let ψ : ↥(commV L) →* Multiplicative (altHeart n) :=
      (AddMonoidHom.toMultiplicative (altAct (θ h)⁻¹)).comp (π.comp R)
    have hψ : ∀ u, Multiplicative.toAdd (ψ u) =
        altAct (θ h)⁻¹ (Multiplicative.toAdd (π (R u))) := fun _ => rfl
    have hk : π.ker ≤ ψ.ker := by
      intro u hu
      rw [hker, Subgroup.mem_subgroupOf] at hu
      have hRu : R u ∈ π.ker := by
        rw [hker, Subgroup.mem_subgroupOf, coe_commVRestrict]
        exact ⟨(R u).2, apply_mem_fixV_of_mem_normalizer (hHN h.2) hu.2⟩
      rw [MonoidHom.mem_ker] at hRu ⊢
      apply Multiplicative.toAdd.injective
      rw [hψ, hRu, toAdd_one, map_zero]
    set g₀ := π.liftOfSurjective hπ ⟨ψ, hk⟩ with hg₀
    have hg₀π : ∀ u, g₀ (π u) = ψ u := fun u => π.liftOfRightInverse_comp_apply _ _ ⟨ψ, hk⟩ u
    set g : altHeart n →+ altHeart n := AddMonoidHom.toMultiplicative.symm g₀ with hg
    have hgπ : ∀ u, g (Multiplicative.toAdd (π u)) =
        altAct (θ h)⁻¹ (Multiplicative.toAdd (π (R u))) := by
      intro u
      rw [← hψ, ← hg₀π]
      rfl
    have hgcomm : ∀ σ ∈ alternatingGroup (Fin n), ∀ v, g (altAct σ v) = altAct σ (g v) := by
      intro σ hσ v
      obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd v)
      obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
      have hv : v = Multiplicative.toAdd (π u) := by rw [hu, toAdd_ofAdd]
      have hσl : σ = (α l : Perm (Fin n)) := by rw [hl]
      have hRR : R (commVRestrict (Subgroup.le_normalizer l.2) u) =
          commVRestrict (Subgroup.le_normalizer (cH h l).2) (R u) := by
        apply Subtype.ext
        rw [coe_commVRestrict, coe_commVRestrict, coe_commVRestrict, coe_commVRestrict,
          hcH_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      rw [hv, hσl, ← hLact, hgπ, hRR, hLact, ← hconj, hgπ, ← altAct_mul, ← altAct_mul]
      congr 1
      group
    rcases altHeart_endo_eq_zero_or_id hn5 g hgcomm with h0 | h1
    · exfalso
      have hall : ∀ w : ↥(commV L), π w = 1 := by
        intro w
        have hinv : (h : MulAut V)⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
          inv_mem (hHN h.2)
        have hw : R (commVRestrict hinv w) = w := by
          apply Subtype.ext
          rw [coe_commVRestrict, coe_commVRestrict, MulAut.apply_inv_self]
        have h2 := hgπ (commVRestrict hinv w)
        rw [h0, AddMonoidHom.zero_apply, hw] at h2
        have h3 := congrArg (altAct (θ h)) h2
        rw [map_zero, altAct_apply_inv] at h3
        exact Multiplicative.toAdd.injective (h3.symm.trans toAdd_one.symm)
      obtain ⟨a, b, hab⟩ := altHeart_nontrivial (n := n) (by omega)
      obtain ⟨wa, hwa⟩ := hπ (Multiplicative.ofAdd a)
      obtain ⟨wb, hwb⟩ := hπ (Multiplicative.ofAdd b)
      rw [hall] at hwa hwb
      exact hab (Multiplicative.ofAdd.injective (hwa.symm.trans hwb))
    · intro u
      have h2 := hgπ u
      rw [h1, AddMonoidHom.id_apply] at h2
      rw [h2, altAct_apply_inv]
  refine ⟨θ, π, hπ, hker, ?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
    exact ⟨l, by rw [MonoidHom.comp_apply, hθL, hl]⟩
  · intro h u v huv x hx
    have hv : v = commVRestrict (hHN h.2) u := Subtype.ext huv
    rw [hv, hHact, hx, altAct_mk]
  · rw [injective_iff_map_eq_one]
    intro h h1
    have hc : autTransport e (cH h) = 1 := by rw [← hcAθ, h1, map_one]
    have hcent : ∀ l : ↥L, cH h l = l := by
      intro l
      have := congrArg (fun φ : MulAut (alternatingGroup (Fin n)) => φ (e l)) hc
      simp only [autTransport_apply, MulAut.one_apply, e.symm_apply_apply] at this
      exact e.injective this
    have hmem : (h : MulAut V) ∈
        H ⊓ Subgroup.centralizer (quasithinGenFitting H : Set (MulAut V)) := by
      refine Subgroup.mem_inf.2 ⟨h.2, ?_⟩
      rw [← hLF, Subgroup.mem_centralizer_iff]
      intro l hl
      have h2 : (h : MulAut V) * l * (h : MulAut V)⁻¹ = l := by
        rw [← hcH_apply h ⟨l, hl⟩, hcent]
      calc l * (h : MulAut V) = (h : MulAut V) * l * (h : MulAut V)⁻¹ * h := by rw [h2]
        _ = h * l := by group
    have hhL : (h : MulAut V) ∈ L := by
      have := centralizer_quasithinGenFitting_le H hmem
      rwa [← hLF] at this
    have h2 := hθL ⟨h, hhL⟩
    rw [show Subgroup.inclusion hLH ⟨(h : MulAut V), hhL⟩ = h from Subtype.ext rfl, h1] at h2
    have h3 : α ⟨h, hhL⟩ = 1 := Subtype.ext h2.symm
    have h4 : (⟨h, hhL⟩ : ↥L) = 1 := hαi (h3.trans (map_one α).symm)
    have h5 : ((⟨h, hhL⟩ : ↥L) : MulAut V) = 1 := congrArg Subtype.val h4
    exact Subtype.ext h5

end CFSG.HardMathSupport.Cooperstein.Coordinator

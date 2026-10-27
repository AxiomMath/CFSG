
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Setup

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank

namespace L246

variable {G : Type} [Group G] [Finite G]

section Maps

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def rho1 {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    ↥K →* ↥(autI hV K) :=
  (convHom hV K hK).codRestrict (autI hV K) fun k => (mem_autI hV).2 ⟨⟨k, hK k.2⟩, k.2, rfl⟩

omit [Finite G] in
theorem rho1_apply {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) (k : ↥K) :
    ((rho1 hV hK k : ↥(autI hV K)) : MulAut (IntMod V hV)) = convI hV ⟨k, hK k.2⟩ := rfl

omit [Finite G] in
theorem rho1_surjective {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (rho1 hV hK) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
  exact ⟨⟨g, hg⟩, Subtype.ext rfl⟩

omit [Finite G] in
theorem mem_ker_rho1 {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) (k : ↥K) :
    k ∈ (rho1 hV hK).ker ↔ (k : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : convI hV ⟨k, hK k.2⟩ = 1 := congrArg Subtype.val h
    exact (convI_eq_one_iff hV ⟨k, hK k.2⟩).1 h1
  · intro h
    exact Subtype.ext ((convI_eq_one_iff hV ⟨k, hK k.2⟩).2 h)

end Maps

structure TrData {G : Type} [Group G] (V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  short : IsShort2 L
  norm : L ≤ Subgroup.normalizer (V : Set G)
  uV : blockU L ≤ V

theorem autI_le_stab {V : Subgroup G} (hV : IsElemAbelian 2 V) (L : Subgroup G) :
    autI hV L ≤ stabSub (intSub hV (blockU L)) ⊓ stabSub (intSub hV (blockZ L)) := by
  intro φ hφ
  obtain ⟨l, hl, rfl⟩ := (mem_autI hV).1 hφ
  exact ⟨convI_mem_stabSub_intSub hV l.2 (C1.le_normalizer_blockU L hl),
    convI_mem_stabSub_intSub hV l.2 (C1.mem_normalizer_blockZ (Subgroup.le_normalizer hl))⟩

namespace TrData

variable {V L : Subgroup G} {hV : IsElemAbelian 2 V} (T : TrData V L hV)

include T

@[expose] noncomputable def rhoSec : ↥L →* ↥(autSec (autI hV L) (intSub hV (blockU L))
    (intSub hV (blockZ L))) :=
  (Bridge.secRestrict (autI_le_stab hV L)).comp (rho1 hV T.norm)

theorem rhoSec_surjective : Function.Surjective T.rhoSec :=
  (Bridge.secRestrict_surjective (autI_le_stab hV L)).comp (rho1_surjective hV T.norm)

@[expose] def uHom : ↥(blockU L) →* ↥(intSub hV (blockU L)) where
  toFun u := ⟨IntMod.mk hV ⟨u, T.uV u.2⟩, u.2⟩
  map_one' := Subtype.ext (IntMod.val_injective rfl)
  map_mul' _ _ := Subtype.ext (IntMod.val_injective rfl)

omit [Finite G] in
theorem uHom_surjective : Function.Surjective T.uHom := by
  rintro ⟨v, hv⟩
  exact ⟨⟨v.val, hv⟩, Subtype.ext (IntMod.val_injective rfl)⟩

@[expose] noncomputable def qHom : ↥(blockU L) →*
    Sec (intSub hV (blockU L)) (intSub hV (blockZ L)) :=
  (QuotientGroup.mk' ((intSub hV (blockZ L)).subgroupOf (intSub hV (blockU L)))).comp T.uHom

omit [Finite G] in
theorem qHom_surjective : Function.Surjective T.qHom :=
  (QuotientGroup.mk'_surjective _).comp T.uHom_surjective

omit [Finite G] in
theorem qHom_eq_one_iff (u : ↥(blockU L)) : T.qHom u = 1 ↔ (u : G) ∈ blockZ L := by
  show (QuotientGroup.mk (T.uHom u) : Sec (intSub hV (blockU L)) (intSub hV (blockZ L))) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact Iff.rfl

omit [Finite G] in
theorem ker_qHom : T.qHom.ker = (blockZ L).subgroupOf (blockU L) := by
  ext u
  rw [MonoidHom.mem_ker, T.qHom_eq_one_iff, Subgroup.mem_subgroupOf]

theorem rhoSec_smul (ℓ : ↥L) (u v : ↥(blockU L)) (h : (v : G) = ℓ * u * ℓ⁻¹) :
    ((T.rhoSec ℓ : ↥(autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L)))) :
        MulAut (Sec (intSub hV (blockU L)) (intSub hV (blockZ L)))) (T.qHom u) = T.qHom v := by
  have hℓ : (ℓ : G) ∈ Subgroup.normalizer (V : Set G) := T.norm ℓ.2
  show Bridge.secHom _ _ (Subgroup.inclusion (autI_le_stab hV L) (rho1 hV T.norm ℓ))
      (QuotientGroup.mk (T.uHom u)) = QuotientGroup.mk (T.uHom v)
  rw [Bridge.secHom_apply]
  congr 1
  apply Subtype.ext
  apply IntMod.val_injective
  show (convI hV ⟨ℓ, hℓ⟩ (IntMod.mk hV ⟨u, T.uV u.2⟩)).val = (v : G)
  rw [convI_apply_val, h]
  rfl

theorem exists_beta {D : FFModel}
    {π : D.Gam →* ↥(autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L)))}
    (hπ : D.RealizesVia (autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L))) ⊤ ⊥ π) :
    ∃ β : ↥(blockU L) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec,
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ (ℓ : ↥L) (γ : D.Gam), π γ = T.rhoSec ℓ → ∀ (u v : ↥(blockU L)) (x : ↥D.sec)
        (hx : D.act γ (x : D.Amb) ∈ D.sec), (v : G) = ℓ * u * ℓ⁻¹ → β u = QuotientGroup.mk x →
          β v = QuotientGroup.mk ⟨D.act γ (x : D.Amb), hx⟩ := by
  obtain ⟨-, -, -, -, -, -, -, β', hβs, hβk, hβe⟩ := hπ
  let t : ↥(blockU L) →* ↥(⊤ : Subgroup (Sec (intSub hV (blockU L)) (intSub hV (blockZ L)))) :=
    (Subgroup.topEquiv.symm : Sec (intSub hV (blockU L)) (intSub hV (blockZ L)) ≃*
      ↥(⊤ : Subgroup (Sec (intSub hV (blockU L)) (intSub hV (blockZ L))))).toMonoidHom.comp T.qHom
  have ht : ∀ u : ↥(blockU L), ((t u : ↥(⊤ : Subgroup (Sec (intSub hV (blockU L))
      (intSub hV (blockZ L))))) : Sec (intSub hV (blockU L)) (intSub hV (blockZ L))) = T.qHom u :=
    fun _ => rfl
  refine ⟨β'.comp t, ?_, ?_, ?_⟩
  · exact hβs.comp ((Subgroup.topEquiv.symm.surjective).comp T.qHom_surjective)
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show β' (t u) = 1 ↔ _
    rw [hβk, Subgroup.mem_bot, ht]
    exact T.qHom_eq_one_iff u
  · intro ℓ γ hγ u v x hx hv hu
    have h1 := hβe γ (t u) x (by trivial) hx hu
    have h2 : (⟨((π γ : ↥(autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L)))) :
        MulAut (Sec (intSub hV (blockU L)) (intSub hV (blockZ L)))) ((t u : ↥(⊤ : Subgroup
        (Sec (intSub hV (blockU L)) (intSub hV (blockZ L))))) :
        Sec (intSub hV (blockU L)) (intSub hV (blockZ L))), trivial⟩ :
        ↥(⊤ : Subgroup (Sec (intSub hV (blockU L)) (intSub hV (blockZ L))))) = t v := by
      apply Subtype.ext
      rw [ht, ht, hγ]
      exact T.rhoSec_smul ℓ u v hv
    show β' (t v) = _
    rw [← h2]
    exact h1

end TrData

section DeltaModule

@[expose] def coreEquiv (m : ℕ) : ↥(FFModel.altDn m).sec ≃* Multiplicative (evenWeight m) where
  toFun x := Multiplicative.ofAdd ⟨Multiplicative.toAdd x.1, x.2⟩
  invFun y := ⟨Multiplicative.ofAdd (Multiplicative.toAdd y : evenWeight m).1,
    (Multiplicative.toAdd y).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem altDn_ker_eq_bot {m : ℕ} (hm : Odd m) : (FFModel.altDn m).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨k, hk⟩, hxc⟩ := hx
  have hsum : ∑ i : Fin m, Multiplicative.toAdd x i = 0 := hxc
  have hxk : ∀ i : Fin m, Multiplicative.toAdd x i = (k : ZMod 2) := by
    intro i
    rw [← hk]
    show Multiplicative.toAdd ((Multiplicative.ofAdd (fun _ : Fin m => (1 : ZMod 2))) ^ k) i = _
    rw [toAdd_zpow]
    simp
  simp only [hxk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hmz : (m : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).2 hm
  rw [hmz, one_mul] at hsum
  have hkz : ∀ i : Fin m, Multiplicative.toAdd x i = 0 := fun i => by
    rw [hxk i, hsum]
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  funext i
  exact hkz i

theorem altDn_ker_subgroupOf_eq_bot {m : ℕ} (hm : Odd m) :
    (FFModel.altDn m).ker.subgroupOf (FFModel.altDn m).sec = ⊥ := by
  rw [altDn_ker_eq_bot hm]
  exact Subgroup.bot_subgroupOf _

@[expose] noncomputable def altQ (m : ℕ) (hm : Odd m) :
    (↥(FFModel.altDn m).sec ⧸ (FFModel.altDn m).ker.subgroupOf (FFModel.altDn m).sec) →*
      Multiplicative (evenWeight m) :=
  QuotientGroup.lift _ (coreEquiv m).toMonoidHom (fun x hx => by
    rw [altDn_ker_subgroupOf_eq_bot hm, Subgroup.mem_bot] at hx
    rw [hx]
    exact MonoidHom.mem_ker.2 (map_one _))

theorem altQ_mk (m : ℕ) (hm : Odd m) (x : ↥(FFModel.altDn m).sec) :
    altQ m hm (QuotientGroup.mk x) = coreEquiv m x := rfl

theorem altQ_eq_one {m : ℕ} (hm : Odd m) {q : ↥(FFModel.altDn m).sec ⧸
    (FFModel.altDn m).ker.subgroupOf (FFModel.altDn m).sec} (h : altQ m hm q = 1) : q = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : coreEquiv m x = 1 := h
  rw [(map_eq_one_iff _ (coreEquiv m).injective).1 h1]
  rfl

end DeltaModule

namespace TrData

variable {V L : Subgroup G} {hV : IsElemAbelian 2 V} (T : TrData V L hV)

include T

theorem isAltType_of_altDn {m : ℕ} (hm : Odd m)
    (hinj : Function.Injective (Bridge.secRestrict (autI_le_stab hV L)))
    (hpc : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer (V : Set G) ↔ l ∈ CFSG.pCore 2 ↥L)
    {π : ↥(alternatingGroup (Fin m)) →*
      ↥(autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L)))}
    (hπ : (FFModel.altDn m).RealizesVia
      (autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L))) ⊤ ⊥ π)
    (hπinj : Function.Injective π) : IsAltType L m := by
  obtain ⟨β, hβs, hβk, hβe⟩ := T.exists_beta hπ
  let eπ := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  let α : ↥L →* alternatingGroup (Fin m) := eπ.symm.toMonoidHom.comp T.rhoSec
  have hαs : Function.Surjective α := eπ.symm.surjective.comp T.rhoSec_surjective
  have hαk : α.ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [MonoidHom.mem_ker]
    show eπ.symm (T.rhoSec l) = 1 ↔ _
    rw [map_eq_one_iff _ eπ.symm.injective, ← hpc]
    constructor
    · intro h
      have h1 : Bridge.secRestrict (autI_le_stab hV L) (rho1 hV T.norm l) = 1 := h
      have h2 : rho1 hV T.norm l = 1 := hinj (h1.trans (map_one _).symm)
      exact (mem_ker_rho1 hV T.norm l).1 h2
    · intro h
      have h2 : rho1 hV T.norm l = 1 := (mem_ker_rho1 hV T.norm l).2 h
      show Bridge.secRestrict (autI_le_stab hV L) (rho1 hV T.norm l) = 1
      rw [h2, map_one]
  refine ⟨α, hαs, hαk, (altQ m hm).comp β, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := (coreEquiv m).surjective y
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk x)
    refine ⟨u, ?_⟩
    show altQ m hm (β u) = y
    rw [hu, altQ_mk, hx]
  · ext u
    have h1 : u ∈ β.ker ↔ u ∈ (blockZ L).subgroupOf (blockU L) := by rw [hβk]
    rw [← h1, MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact altQ_eq_one hm h
    · intro h
      show altQ m hm (β u) = 1
      rw [h, map_one]
  · intro ℓ u v hv i
    have hπγ : π (α ℓ) = T.rhoSec ℓ := eπ.apply_symm_apply _
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β u)
    have hx' : (FFModel.altDn m).act (α ℓ) x.1 ∈ (FFModel.altDn m).sec :=
      hπ.2.2.2.2.2.1 (α ℓ) x x.2
    have h1 := hβe ℓ (α ℓ) hπγ u v x hx' hv hx.symm
    show ((Multiplicative.toAdd (altQ m hm (β v)) : evenWeight m) : Fin m → ZMod 2) i =
      ((Multiplicative.toAdd (altQ m hm (β u)) : evenWeight m) : Fin m → ZMod 2)
        (((α ℓ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m))⁻¹ i)
    rw [h1, ← hx, altQ_mk, altQ_mk]
    rfl

theorem isLin2Type_of_nat {K : Type} [Field K] [Finite K] {n : ℕ} (hKn : Nat.card K = 2 ^ n)
    (hinj : Function.Injective (Bridge.secRestrict (autI_le_stab hV L)))
    (hpc : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer (V : Set G) ↔ l ∈ CFSG.pCore 2 ↥L)
    {π : ↥(StatedSL 2 K) →*
      ↥(autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L)))}
    (hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia
      (autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L))) ⊤ ⊥ π)
    (hπinj : Function.Injective π) : IsLin2Type L n := by
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨β, hβs, hβk, hβe⟩ := T.exists_beta hπ
  let eπ := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  let eSL := specialLinearGroupEquivStatedSL 2 K
  let α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K :=
    eSL.symm.toMonoidHom.comp (eπ.symm.toMonoidHom.comp T.rhoSec)
  have hαs : Function.Surjective α :=
    eSL.symm.surjective.comp (eπ.symm.surjective.comp T.rhoSec_surjective)
  have hαk : α.ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [MonoidHom.mem_ker]
    show eSL.symm (eπ.symm (T.rhoSec l)) = 1 ↔ _
    rw [map_eq_one_iff _ eSL.symm.injective, map_eq_one_iff _ eπ.symm.injective, ← hpc]
    constructor
    · intro h
      have h1 : Bridge.secRestrict (autI_le_stab hV L) (rho1 hV T.norm l) = 1 := h
      have h2 : rho1 hV T.norm l = 1 := hinj (h1.trans (map_one _).symm)
      exact (mem_ker_rho1 hV T.norm l).1 h2
    · intro h
      have h2 : rho1 hV T.norm l = 1 := (mem_ker_rho1 hV T.norm l).2 h
      show Bridge.secRestrict (autI_le_stab hV L) (rho1 hV T.norm l) = 1
      rw [h2, map_one]
  let natQ : (↥(FFModel.nat (StatedSL 2 K)).sec ⧸
      (FFModel.nat (StatedSL 2 K)).ker.subgroupOf (FFModel.nat (StatedSL 2 K)).sec) →*
      Multiplicative (Fin 2 → K) :=
    QuotientGroup.lift _ (Subgroup.subtype (FFModel.nat (StatedSL 2 K)).sec) (fun x hx => by
      have h1 : x.1 ∈ (⊥ : Subgroup (Multiplicative (Fin 2 → K))) :=
        Subgroup.mem_subgroupOf.1 hx
      exact Subgroup.mem_bot.1 h1)
  have hq : ∀ q, natQ q = 1 → q = 1 := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : x.1 = 1 := hq
    have h2 : x = 1 := Subtype.ext h1
    rw [h2]
    rfl
  refine ⟨K, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card]; exact hKn, α, hαs,
    hαk, natQ.comp β, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk (⟨y, trivial⟩ : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))))
    exact ⟨u, by show natQ (β u) = y; rw [hu]; rfl⟩
  · ext u
    have h1 : u ∈ β.ker ↔ u ∈ (blockZ L).subgroupOf (blockU L) := by rw [hβk]
    rw [← h1, MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact hq _ h
    · intro h
      show natQ (β u) = 1
      rw [h, map_one]
  · intro ℓ u v hv
    have hπγ : π (eπ.symm (T.rhoSec ℓ)) = T.rhoSec ℓ := eπ.apply_symm_apply _
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β u)
    have hx' : (FFModel.nat (StatedSL 2 K)).act (eπ.symm (T.rhoSec ℓ))
        x.1 ∈ (FFModel.nat (StatedSL 2 K)).sec := trivial
    have h1 := hβe ℓ (eπ.symm (T.rhoSec ℓ)) hπγ u v x hx' hv hx.symm
    show Multiplicative.toAdd (natQ (β v)) =
      ((α ℓ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (natQ (β u)))
    rw [h1, ← hx]
    have hcoe : ((α ℓ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (((eπ.symm (T.rhoSec ℓ) : ↥(StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) := by
      have := specialLinearGroupEquivStatedSL_coe 2 K (eSL.symm (eπ.symm (T.rhoSec ℓ)))
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [hcoe]
    rfl

theorem isExcA7Block_of_card
    (hinj : Function.Injective (Bridge.secRestrict (autI_le_stab hV L)))
    (hpc : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer (V : Set G) ↔ l ∈ CFSG.pCore 2 ↥L)
    (e : ↥(autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L))) ≃*
      alternatingGroup (Fin 7))
    (hcard : Nat.card (Sec (intSub hV (blockU L)) (intSub hV (blockZ L))) = 2 ^ 4) :
    IsExcA7Block L := by
  let α : ↥L →* alternatingGroup (Fin 7) := e.toMonoidHom.comp T.rhoSec
  have hαs : Function.Surjective α := e.surjective.comp T.rhoSec_surjective
  have hαk : α.ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [MonoidHom.mem_ker]
    show e (T.rhoSec l) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, ← hpc]
    constructor
    · intro h
      have h1 : Bridge.secRestrict (autI_le_stab hV L) (rho1 hV T.norm l) = 1 := h
      have h2 : rho1 hV T.norm l = 1 := hinj (h1.trans (map_one _).symm)
      exact (mem_ker_rho1 hV T.norm l).1 h2
    · intro h
      have h2 : rho1 hV T.norm l = 1 := (mem_ker_rho1 hV T.norm l).2 h
      show Bridge.secRestrict (autI_le_stab hV L) (rho1 hV T.norm l) = 1
      rw [h2, map_one]
  refine ⟨T.short, ⟨α, hαs, hαk⟩, ?_⟩
  rw [← T.ker_qHom, Subgroup.index_ker, MonoidHom.range_eq_top.2 T.qHom_surjective,
    Subgroup.card_top]
  exact hcard

end TrData

end L246

end CFSG.QuasithinUnique

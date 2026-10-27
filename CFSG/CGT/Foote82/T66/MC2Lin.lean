module

public import CFSG.CGT.Foote82.T66.Basic
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.Open CFSG.Quasithin.G11

section Order3

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def cfix (x : GLV W) : Submodule (ZMod 2) W :=
  LinearMap.ker ((x : W →ₗ[ZMod 2] W) - LinearMap.id)

@[expose] def comm1 (x : GLV W) : Submodule (ZMod 2) W :=
  LinearMap.range ((x : W →ₗ[ZMod 2] W) - LinearMap.id)

theorem mem_cfix {x : GLV W} {v : W} : v ∈ cfix x ↔ x v = v := by
  simp [cfix, sub_eq_zero]

theorem mem_comm1 {x : GLV W} {v : W} : v ∈ comm1 x ↔ ∃ u, x u - u = v := by
  simp [comm1]

theorem add_add_eq_zero_of_mem_comm1 {x : GLV W} (hx : ∀ v, x (x (x v)) = v) {v : W}
    (hv : v ∈ comm1 x) : v + x v + x (x v) = 0 := by
  obtain ⟨u, rfl⟩ := mem_comm1.1 hv
  simp only [map_sub, hx]
  abel

theorem cfix_inf_comm1 {x : GLV W} (hx : ∀ v, x (x (x v)) = v) : cfix x ⊓ comm1 x = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv1, hv2⟩
  have h := add_add_eq_zero_of_mem_comm1 hx hv2
  rw [mem_cfix.1 hv1, mem_cfix.1 hv1, ZModModule.add_self, zero_add] at h
  exact h

theorem cfix_sup_comm1 {x : GLV W} (hx : ∀ v, x (x (x v)) = v) : cfix x ⊔ comm1 x = ⊤ := by
  rw [eq_top_iff]
  intro v _
  refine Submodule.mem_sup.2 ⟨v + x v + x (x v), ?_, x (x v) - x v, mem_comm1.2 ⟨x v, rfl⟩, ?_⟩
  · rw [mem_cfix]
    simp only [map_add, hx]
    abel
  · calc v + x v + x (x v) + (x (x v) - x v) = v + (x (x v) + x (x v)) := by abel
      _ = v := by rw [ZModModule.add_self, add_zero]

theorem comm1_spec {x : GLV W} (hx : ∀ v, x (x (x v)) = v) {v : W} (hv : v ∈ comm1 x) :
    x (x v) - x v = v := by
  obtain ⟨u, rfl⟩ := mem_comm1.1 hv
  simp only [map_sub, hx]
  have h2 : (u - x (x u)) + (u - x (x u)) = 0 := ZModModule.add_self _
  calc u - x (x u) - (x (x u) - x u) = x u - u + ((u - x (x u)) + (u - x (x u))) := by abel
    _ = x u - u := by rw [h2, add_zero]

theorem fpf_of_comm1_eq_top {x : GLV W} (hx : ∀ v, x (x (x v)) = v) (h : comm1 x = ⊤) :
    ∀ v, x v = v → v = 0 := by
  intro v hv
  have : v ∈ cfix x ⊓ comm1 x := ⟨mem_cfix.2 hv, h ▸ Submodule.mem_top⟩
  rw [cfix_inf_comm1 hx] at this
  exact this

theorem cfix_eq_comm1 {x y : GLV W} (hx : ∀ v, x (x (x v)) = v) (hy : ∀ v, y (y (y v)) = v)
    (hxy : ∀ v, x (y v) = y (x v)) (h1 : ∀ v, x (y v) = v → v = 0)
    (h2 : ∀ v, x (y (y v)) = v → v = 0) : cfix x = comm1 y := by
  ext v
  rw [mem_cfix]
  constructor
  · intro hv
    set w₁ := y (y v) + y v + v with hw₁
    have hyw : y w₁ = w₁ := by
      rw [hw₁]
      simp only [map_add, hy]
      abel
    have hxw : x w₁ = w₁ := by
      rw [hw₁]
      simp only [map_add, hxy, hv]
    have hw0 : w₁ = 0 := h1 w₁ (by rw [hyw, hxw])
    refine mem_comm1.2 ⟨y v, ?_⟩
    have e : y (y v) = -(y v + v) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]
      exact hw0
    rw [e, ZModModule.neg_eq_self]
    abel
  · intro hv
    have hr : v + y v + y (y v) = 0 := add_add_eq_zero_of_mem_comm1 hy hv
    have hr' : y (y v) = -v - y v := by
      rw [← sub_eq_zero]
      calc y (y v) - (-v - y v) = v + y v + y (y v) := by abel
        _ = 0 := hr
    set z := x v - v with hz
    set q := x z - y (y z) with hq
    have hP : x q - y q = 0 := by
      rw [hq, hz]
      simp only [map_sub, ← hxy, hx, hy, hr', map_neg]
      abel
    have hq0 : q = 0 := by
      refine h2 q ?_
      have e1 : x q = y q := sub_eq_zero.1 hP
      calc x (y (y q)) = y (y (x q)) := by rw [hxy, hxy]
        _ = y (y (y q)) := by rw [e1]
        _ = q := hy q
    have hz0 : z = 0 := by
      refine h1 z ?_
      have e1 : x z = y (y z) := sub_eq_zero.1 (hq ▸ hq0)
      calc x (y z) = y (x z) := hxy z
        _ = y (y (y z)) := by rw [e1]
        _ = z := hy z
    exact sub_eq_zero.1 hz0

theorem eq_bot_of_chain {e₁ e₂ e₃ e₄ e₅ e₆ e₇ : GLV W} (h7 : ∀ v, e₇ (e₇ (e₇ v)) = v)
    (h12 : cfix e₁ = comm1 e₂) (h32 : cfix e₃ = comm1 e₂) (h34 : cfix e₃ = comm1 e₄)
    (h54 : cfix e₅ = comm1 e₄) (h56 : cfix e₅ = comm1 e₆) (h76 : cfix e₇ = comm1 e₆)
    (h17 : cfix e₁ = comm1 e₇) : (⊤ : Submodule (ZMod 2) W) = ⊥ := by
  have hc : cfix e₇ = comm1 e₇ := by
    rw [← h17, h12, ← h32, h34, ← h54, h56, ← h76]
  have hb : cfix e₇ = ⊥ := by
    rw [← inf_idem (cfix e₇)]
    nth_rewrite 2 [hc]
    exact cfix_inf_comm1 h7
  rw [← cfix_sup_comm1 h7, ← hc, hb, sup_bot_eq]

end Order3

section TildeV

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem conj_mem_self (L : Subgroup (GLV V)) : ∀ k' ∈ L, ∀ k ∈ L, k' * k * k'⁻¹ ∈ L :=
  fun _ hk' _ hk => L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk')

theorem invariant_fixedSpace_self (L : Subgroup (GLV V)) : Invariant L (fixedSpace L) :=
  invariant_fixedSpace (conj_mem_self L)

theorem invariant_commSpace_self (L : Subgroup (GLV V)) : Invariant L (commSpace L ⊤) :=
  invariant_commSpace (conj_mem_self L) (invariant_top L)

noncomputable abbrev rhoT (L : Subgroup (GLV V)) : ↥L →* GLV (TildeV L) :=
  sectHom L (invariant_fixedSpace_self L) (invariant_commSpace_self L)

theorem rhoT_mk (L : Subgroup (GLV V)) (ℓ : ↥L) (w : ↥(commSpace L ⊤)) :
    rhoT L ℓ (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨(ℓ : GLV V) w, invariant_commSpace_self L ℓ ℓ.2 w w.2⟩ :=
  sectHom_mk _ _ _ ℓ w

theorem mk_eq_mk_iff (L : Subgroup (GLV V)) {v v' : V} (hv : v ∈ commSpace L ⊤)
    (hv' : v' ∈ commSpace L ⊤) :
    (Submodule.Quotient.mk ⟨v, hv⟩ : TildeV L) = Submodule.Quotient.mk ⟨v', hv'⟩ ↔
      v - v' ∈ fixedSpace L := by
  rw [Submodule.Quotient.eq]
  rfl

theorem rhoT_injective {L : Subgroup (GLV V)} (hf : FaithfulTildeV L) :
    Function.Injective (rhoT L) := by
  rw [injective_iff_map_eq_one]
  intro ℓ hℓ
  apply Subtype.ext
  refine hf ℓ ℓ.2 fun w hw => ?_
  have h' := congrArg (fun f : GLV (TildeV L) => f (Submodule.Quotient.mk ⟨w, hw⟩)) hℓ
  simp only [rhoT_mk] at h'
  exact (mk_eq_mk_iff L _ hw).1 h'

theorem isIrr_range_rhoT {L : Subgroup (GLV V)} (hirr : HasIrrTildeV L) :
    IsIrr (rhoT L).range ⊤ := by
  obtain ⟨hlt, hmin⟩ := hirr
  refine ⟨invariant_top _, ⟨bot_lt_iff_ne_bot.2 ?_, fun J hJ _ _ => ?_⟩⟩
  ·
    intro htop
    obtain ⟨w, hw, hwC⟩ := SetLike.exists_of_lt hlt
    have : (Submodule.Quotient.mk ⟨w, hw⟩ : TildeV L) ∈ (⊤ : Submodule (ZMod 2) (TildeV L)) :=
      Submodule.mem_top
    rw [htop, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at this
    exact hwC ⟨this, hw⟩
  ·
    set A := commSpace L ⊤ with hA
    set J' : Submodule (ZMod 2) V :=
      (J.comap ((fixedSpace L).comap A.subtype).mkQ).map A.subtype with hJ'
    have hmemJ' : ∀ (v : V) (hv : v ∈ A), v ∈ J' ↔
        (Submodule.Quotient.mk ⟨v, hv⟩ : TildeV L) ∈ J := by
      intro v hv
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro h
        exact ⟨⟨v, hv⟩, h, rfl⟩
    have hJ'A : J' ≤ A := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hCJ' : tildeVBot L ≤ J' := by
      rintro v ⟨hvC, hvA⟩
      rw [hmemJ' v hvA]
      have : (Submodule.Quotient.mk ⟨v, hvA⟩ : TildeV L) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hvC
      rw [this]
      exact J.zero_mem
    have hJ'inv : Invariant L J' := by
      intro ℓ hℓ v hv
      have hvA := hJ'A hv
      have hℓv : ℓ v ∈ A := invariant_commSpace_self L ℓ hℓ v hvA
      rw [hmemJ' v hvA] at hv
      rw [hmemJ' _ hℓv]
      have := hJ (rhoT L ⟨ℓ, hℓ⟩) ⟨⟨ℓ, hℓ⟩, rfl⟩ _ hv
      rwa [rhoT_mk] at this
    rcases hmin J' hJ'inv hCJ' hJ'A with h | h
    · left
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hvJ' : v ∈ J' := (hmemJ' v hv).2 hq
      rw [h] at hvJ'
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact hvJ'.1
    · right
      rw [eq_top_iff]
      intro q _
      obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hvJ' : v ∈ J' := h ▸ hv
      exact (hmemJ' v hv).1 hvJ'

theorem commSpace_zpowers_le_comm1 (x : GLV V) :
    commSpace (Subgroup.zpowers x) ⊤ ≤ comm1 x := by
  have hfin : IsOfFinOrder x := isOfFinOrder_of_finite x
  refine commSpace_le_iff.2 fun k hk u _ => ?_
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, x ^ n = k := by
    have := (hfin.mem_powers_iff_mem_zpowers).2 hk
    exact Submonoid.mem_powers_iff _ _ |>.1 this
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (x ^ (n + 1)) u - u = (x ((x ^ n) u) - (x ^ n) u) + ((x ^ n) u - u) := by
      rw [pow_succ', LinearEquiv.mul_apply]
      abel
    rw [e]
    exact (comm1 x).add_mem (mem_comm1.2 ⟨_, rfl⟩) (ih (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) n))

theorem comm1_le_commSpace {L : Subgroup (GLV V)} {x : GLV V} (hx : x ∈ L) :
    comm1 x ≤ commSpace L ⊤ := by
  intro v hv
  obtain ⟨u, rfl⟩ := mem_comm1.1 hv
  exact sub_mem_commSpace hx Submodule.mem_top

theorem finrank_comm1_le {L : Subgroup (GLV V)} (x : ↥L)
    (hx : ∀ v, (x : GLV V) ((x : GLV V) ((x : GLV V) v)) = v) :
    Module.finrank (ZMod 2) ↥(comm1 (x : GLV V)) ≤
      Module.finrank (ZMod 2) ↥(comm1 (rhoT L x)) := by
  set A := commSpace L ⊤ with hA
  have hle : comm1 (x : GLV V) ≤ A := comm1_le_commSpace x.2
  let g : ↥(comm1 (x : GLV V)) →ₗ[ZMod 2] TildeV L :=
    ((fixedSpace L).comap A.subtype).mkQ ∘ₗ Submodule.inclusion hle
  have hg : ∀ v : ↥(comm1 (x : GLV V)), g v ∈ comm1 (rhoT L x) := by
    rintro ⟨v, hv⟩
    have hxv : (x : GLV V) v ∈ A := invariant_commSpace_self L x x.2 v (hle hv)
    refine mem_comm1.2 ⟨Submodule.Quotient.mk ⟨(x : GLV V) v, hxv⟩, ?_⟩
    rw [rhoT_mk, ← Submodule.Quotient.mk_sub]
    change _ = (Submodule.Quotient.mk (⟨v, hle hv⟩ : ↥A) : TildeV L)
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_sub]
    exact comm1_spec hx hv
  let f : ↥(comm1 (x : GLV V)) →ₗ[ZMod 2] ↥(comm1 (rhoT L x)) := g.codRestrict _ hg
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨v, hv⟩ hv0
    rw [LinearMap.mem_ker] at hv0
    have hv0' : (Submodule.Quotient.mk (⟨v, hle hv⟩ : ↥A) : TildeV L) = 0 :=
      congrArg Subtype.val hv0
    have hC : v ∈ fixedSpace L :=
      (Submodule.Quotient.mk_eq_zero ((fixedSpace L).comap A.subtype)).1 hv0'
    have hfix : (x : GLV V) v = v := hC x x.2
    have : v ∈ cfix (x : GLV V) ⊓ comm1 (x : GLV V) := ⟨mem_cfix.2 hfix, hv⟩
    rw [cfix_inf_comm1 hx] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext this
  exact LinearMap.finrank_le_finrank_of_injective hf

theorem finrank_commSpace_le {L : Subgroup (GLV V)} (x : ↥L)
    (hx : ∀ v, (x : GLV V) ((x : GLV V) ((x : GLV V) v)) = v) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (x : GLV V)) ⊤) ≤
      Module.finrank (ZMod 2) ↥(comm1 (rhoT L x)) :=
  (Submodule.finrank_mono (commSpace_zpowers_le_comm1 _)).trans (finrank_comm1_le x hx)

end TildeV

end MC2

end CFSG.CGT.Foote82

module

public import CFSG.CGT.PushingUpLit.SolK.FourTheta
public import CFSG.CGT.PushingUpLit.SolK.TI

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

abbrev CGOf {G : Type} [Group G] (x : G) : Subgroup G :=
  Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)

theorem sup_norm {G : Type} [Group G] {M : Subgroup G} {x k t : G} (hk : k ∈ CMOf M x)
    (ht : t ∈ pCoreOf 2 (CGOf x) ⊔ pCoreOf 2 M) :
    k * t * k⁻¹ ∈ pCoreOf 2 (CGOf x) ⊔ pCoreOf 2 M := by
  have hle : (pCoreOf 2 (CGOf x) ⊔ pCoreOf 2 M).map (MulAut.conj k).toMonoidHom ≤
      pCoreOf 2 (CGOf x) ⊔ pCoreOf 2 M := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact pCoreOf_normalized (CGOf x) (Subgroup.mem_inf.1 hk).2 hz
    · rintro _ ⟨z, hz, rfl⟩
      exact pCoreOf_normalized M (Subgroup.mem_inf.1 hk).1 hz
  exact hle ⟨t, ht, rfl⟩

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem mul_mem_Q {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) : w * r ∈ pCoreOf 2 M :=
  (pCoreOf 2 M).mul_mem (S.W_le_Q hw) hr.1

theorem Q_le_CGOf (hT : TightData S) {x : G} (hx : x ∈ pCoreOf 2 M) : pCoreOf 2 M ≤ CGOf x :=
  fun q hq => mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 (hT.abelian q hq x hx))

theorem Q_le_TOf (hT : TightData S) {x : G} (hx : x ∈ pCoreOf 2 M) :
    pCoreOf 2 M ≤ TOf M x := by
  refine le_pCoreOf_of_normalized (fun q hq => Subgroup.mem_inf.2 ⟨pCoreOf_le_self M hq,
    S.Q_le_CGOf hT hx hq⟩) (fun k hk q hq => pCoreOf_normalized M (Subgroup.mem_inf.1 hk).1 hq)
    (isPGroup_pCoreOf' M)

theorem mul_ne_one {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hpos : 0 < (vsupp (S.D.β ⟨w, hw⟩)).card) : w * r ≠ 1 := by
  intro h
  have hwr : w = r⁻¹ := eq_inv_of_mul_eq_one_left h
  have hw1 : w = 1 := S.W_inf_R hw (hwr ▸ (rOf M X).inv_mem hr)
  subst hw1
  have : S.D.β ⟨1, hw⟩ = 1 := by
    have h1 : (⟨1, hw⟩ : ↥S.D.W) = 1 := rfl
    rw [h1, map_one]
  rw [this] at hpos
  have : vsupp (1 : ↥(coreMod (2 * n + 1))) = ∅ := by
    ext i
    simp [mem_vsupp, vcoord_one]
  rw [this] at hpos
  simp at hpos

theorem Q_le_normalizer_P (hT : TightData S) {x : G} (hxQ : x ∈ pCoreOf 2 M) :
    pCoreOf 2 M ≤ Subgroup.normalizer ((pCoreOf 2 (CGOf x) : Subgroup G) : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro p
  have hqK : q ∈ CGOf x := S.Q_le_CGOf hT hxQ hq
  refine ⟨fun hp => pCoreOf_normalized _ hqK hp, fun hp => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hqK) hp
  simpa [mul_assoc] using this

theorem isPGroup_sup (hT : TightData S) {x : G} (hxQ : x ∈ pCoreOf 2 M) :
    IsPGroup 2 (pCoreOf 2 (CGOf x) ⊔ pCoreOf 2 M : Subgroup G) :=
  (isPGroup_pCoreOf' (CGOf x)).to_sup_of_normal_left' (isPGroup_pCoreOf' M)
    (S.Q_le_normalizer_P hT hxQ)

theorem sup_inf_le_TOf (hT : TightData S) {x : G} (hxQ : x ∈ pCoreOf 2 M) :
    (pCoreOf 2 (CGOf x) ⊔ pCoreOf 2 M) ⊓ M ≤ TOf M x := by
  have hT2 := S.isPGroup_sup hT hxQ
  have hTK : pCoreOf 2 (CGOf x) ⊔ pCoreOf 2 M ≤ CGOf x :=
    sup_le (pCoreOf_le_self _) (S.Q_le_CGOf hT hxQ)
  refine le_pCoreOf_of_normalized (fun t ht => ⟨ht.2, hTK ht.1⟩) (fun k hk z hz => ?_)
    (isPGroup_of_le hT2 inf_le_left)
  exact Subgroup.mem_inf.2 ⟨sup_norm hk hz.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.1
    hz.2) (M.inv_mem hk.1)⟩

theorem mem_M_of_conj_Q {g : G} (h1 : ∀ q ∈ pCoreOf 2 M, g * q * g⁻¹ ∈ pCoreOf 2 M)
    (h2 : ∀ q ∈ pCoreOf 2 M, g⁻¹ * q * g ∈ pCoreOf 2 M) : g ∈ M := by
  rw [← S.normalizer_Q_eq, Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨h1 q, fun hq => ?_⟩
  have := h2 _ hq
  simpa [mul_assoc] using this

theorem normalizer_TOf_le_M (hT : TightData S) (hQe : QElem S) {w r : G} (hw : w ∈ S.D.W)
    (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4) :
    Subgroup.normalizer ((TOf M (w * r) : Subgroup G) : Set G) ≤ M := by
  have key : ∀ g ∈ Subgroup.normalizer ((TOf M (w * r) : Subgroup G) : Set G),
      ∀ q ∈ pCoreOf 2 M, g * q * g⁻¹ ∈ pCoreOf 2 M := by
    intro g hg
    have hQT := S.Q_le_TOf hT (S.mul_mem_Q hw hr)
    have hET : conjSubgroup g (pCoreOf 2 M) ≤ TOf M (w * r) := by
      intro e he
      have he' : g⁻¹ * e * g ∈ pCoreOf 2 M := mem_conjSubgroup.1 he
      have h1 := hQT he'
      have h2 := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * e * g)).1 h1
      have : g * (g⁻¹ * e * g) * g⁻¹ = e := by group
      rwa [this] at h2
    obtain ⟨-, hEq⟩ := S.elem_le_of_len_four hT hw hr hcard hET (S.elemAbelian_conj hT hQe g)
    have hcardg : Nat.card ↥(conjSubgroup g (pCoreOf 2 M)) = Nat.card ↥(pCoreOf 2 M) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hEq' := hEq hcardg
    intro q hq
    have : g * q * g⁻¹ ∈ conjSubgroup g (pCoreOf 2 M) := by
      refine mem_conjSubgroup.2 ?_
      have e : g⁻¹ * (g * q * g⁻¹) * g = q := by group
      rw [e]
      exact hq
    rwa [hEq'] at this
  intro g hg
  exact S.mem_M_of_conj_Q (key g hg) (fun q hq => by
    simpa using key g⁻¹ ((Subgroup.normalizer _).inv_mem hg) q hq)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK

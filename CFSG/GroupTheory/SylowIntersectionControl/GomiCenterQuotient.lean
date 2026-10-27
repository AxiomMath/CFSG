module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.GroupTheory.OddKernelImage
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentClauses
import CFSG.Holt.Induced
import CFSG.Quasithin.Background.E1Amb

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section TwoResidual

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_of_mk'_mem_map {Z X Q : Subgroup G} [Z.Normal]
    (hZX : Z ≤ centralizer (X : Set G)) (hZ : Nat.Coprime (Nat.card Z) 2) (hQX : Q ≤ X)
    (hQ : IsPGroup 2 Q) {y : G} (hy : QuotientGroup.mk' Z y ∈ Q.map (QuotientGroup.mk' Z))
    {n : ℕ} (hyn : y ^ 2 ^ n = 1) : y ∈ Q := by
  obtain ⟨q, hq, hqy⟩ := mem_map.mp hy
  obtain ⟨z, hz, rfl⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hqy
  obtain ⟨m, hm⟩ := hQ ⟨q, hq⟩
  have hqm : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hpow : z ^ 2 ^ (m + n) = 1 := by
    have h := Commute.mul_pow (mem_centralizer_iff.mp (hZX hz) q (hQX hq)) (2 ^ (m + n))
    rw [pow_add, pow_mul', hyn, one_pow, pow_mul, hqm, one_pow, one_mul] at h
    rw [pow_add]
    exact h.symm
  have hord : orderOf z = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (Z.orderOf_dvd_natCard hz) (Nat.Coprime.pow_right _ hZ))
      (orderOf_dvd_of_pow_eq_one hpow)
  rw [orderOf_eq_one_iff] at hord
  rwa [hord, mul_one]

private theorem pCoreOf_map_le_map_pCoreOf {Z X : Subgroup G} [Z.Normal]
    (hZX : Z ≤ centralizer (X : Set G)) (hZ : Nat.Coprime (Nat.card Z) 2) :
    pCoreOf 2 (X.map (QuotientGroup.mk' Z)) ≤ (pCoreOf 2 X).map (QuotientGroup.mk' Z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, -, hPX, hP, hPV⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le (H := X)
    (QuotientGroup.mk' Z) (LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (LieType.BorelTits.pCoreOf_le 2 _) IsPGroup.of_bot bot_le
    (by rw [Subgroup.map_bot]; exact bot_le)
  have key : ∀ g ∈ X, ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine mem_of_mk'_mem_map hZX hZ hPX hP ?_ (n := n)
      (by rw [conj_pow, hxn, mul_one, mul_inv_cancel])
    rw [hPV, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (mem_map_of_mem _ hg)) _).mp (by rw [← hPV]; exact mem_map_of_mem _ hx)
  rw [← hPV]
  refine map_mono (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPX (fun g hg =>
    mem_normalizer_iff.mpr fun x => ⟨key g hg x, fun hx => ?_⟩) hP)
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hx

theorem twoResidual_inf_centralizer_le_comap {N Z : Subgroup G} [N.Normal] [Z.Normal]
    (hGN : IsPGroup 2 (G ⧸ N)) (hZN : Z ≤ centralizer (N : Set G))
    (hZ : Nat.Coprime (Nat.card Z) 2) {M W : Subgroup (G ⧸ Z)}
    (hMW : twoResidual (M ⊓ N.map (QuotientGroup.mk' Z) ⊓
      centralizer (pCoreOf 2 (M ⊓ N.map (QuotientGroup.mk' Z)) : Set (G ⧸ Z))) ≤ W) :
    twoResidual (M.comap (QuotientGroup.mk' Z) ⊓
      centralizer (pCoreOf 2 (M.comap (QuotientGroup.mk' Z)) : Set G)) ≤
        W.comap (QuotientGroup.mk' Z) := by
  set X := M.comap (QuotientGroup.mk' Z) ⊓ N
  have hX : X.map (QuotientGroup.mk' Z) = M ⊓ N.map (QuotientGroup.mk' Z) := by
    refine le_antisymm (le_inf ((map_mono inf_le_left).trans (map_comap_le _ _))
      (map_mono inf_le_right)) ?_
    rintro _ ⟨hm, n, hn, rfl⟩
    exact mem_map_of_mem _ ⟨hm, hn⟩
  have hZX : Z ≤ centralizer (X : Set G) := hZN.trans (centralizer_le inf_le_right)
  refine (twoResidual_inf_centralizer_le_inf hGN _).trans ?_
  rw [← map_le_iff_le_comap]
  refine (E1.map_twoResidual _ _).le.trans ((E1.twoResidual_mono ?_).trans hMW)
  rw [← hX]
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨mem_map_of_mem _ hy.1, mem_centralizer_iff.mpr fun o ho => ?_⟩
  obtain ⟨o', ho', rfl⟩ := pCoreOf_map_le_map_pCoreOf hZX hZ ho
  rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hy.2 o' ho']

end TwoResidual

section Quotient

variable {G : Type} [Group G]

theorem GomiConjugatesCommute.map {G' : Type} [Group G'] {L : Subgroup G}
    (h : GomiConjugatesCommute L) {φ : G →* G'} (hφ : Function.Surjective φ) :
    GomiConjugatesCommute (L.map φ) where
  commute g' hg' := by
    obtain ⟨g, rfl⟩ := hφ g'
    have hc : (L.map φ).map (MulAut.conj (φ g)).toMonoidHom =
        (L.map (MulAut.conj g).toMonoidHom).map φ := by
      rw [map_map, map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    rw [hc] at hg' ⊢
    rw [← map_commutator, h.commute g fun he => hg' (by rw [he]), Subgroup.map_bot]
  isPGroup_quotient := by
    have hle : (normalClosure (L : Set G)).map φ ≤
        normalClosure ((L.map φ : Subgroup G') : Set G') := by
      rw [coe_map]
      exact map_normalClosure_le _ _
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨g, rfl⟩ := hφ x
      obtain ⟨k, hk⟩ := h.isPGroup_quotient (g : G ⧸ normalClosure (L : Set G))
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← map_pow]
      exact hle (mem_map_of_mem φ ((QuotientGroup.eq_one_iff _).mp
        (by rw [QuotientGroup.mk_pow]; exact hk)))

theorem inf_centralizer_map_mk'_eq_bot {L Z : Subgroup G} [Z.Normal]
    (hL : CFSG.IsQuasisimple ↥L) (hZ : Z.subgroupOf L = center ↥L) :
    L.map (QuotientGroup.mk' Z) ⊓ centralizer (L.map (QuotientGroup.mk' Z) : Set (G ⧸ Z)) = ⊥ := by
  have hbot : center (↥L ⧸ center ↥L) = ⊥ := by
    obtain ⟨-, hs, a, b, hab⟩ := hL
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right fun ht =>
      hab (mem_center_iff.mp (ht ▸ mem_top b) a)
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨⟨x, hx, rfl⟩, hc⟩
  have hcen : (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ center ↥L) ∈ center (↥L ⧸ center ↥L) := by
    refine mem_center_iff.mpr fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H l =>
      have h1 := mem_centralizer_iff.mp hc _ (mem_map_of_mem (QuotientGroup.mk' Z) l.2)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, ← hZ, mem_subgroupOf]
      exact h1
  rw [hbot, mem_bot, QuotientGroup.eq_one_iff, ← hZ, mem_subgroupOf] at hcen
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hcen

theorem isSylowTwoOf_inf_map_mk'_iff [Finite G] {N Z H : Subgroup G} [Z.Normal]
    (hZ : Nat.Coprime (Nat.card Z) 2) (hZN : Z ≤ N) (hH : IsPGroup 2 H) :
    IsSylowTwoOf (H.map (QuotientGroup.mk' Z) ⊓ N.map (QuotientGroup.mk' Z))
        (N.map (QuotientGroup.mk' Z)) ↔ IsSylowTwoOf (H ⊓ N) N := by
  have hJ : H.map (QuotientGroup.mk' Z) ⊓ N.map (QuotientGroup.mk' Z) =
      (H ⊓ N).map (QuotientGroup.mk' Z) := by
    refine le_antisymm ?_ (le_inf (map_mono inf_le_left) (map_mono inf_le_right))
    rintro _ ⟨⟨h, hh, rfl⟩, n, hn, hhn⟩
    obtain ⟨z, hz, rfl⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hhn
    exact mem_map_of_mem _ ⟨hh, mul_mem hn (hZN hz)⟩
  have h2 : IsPGroup 2 ↥(H ⊓ N) := hH.to_le inf_le_left
  have hJN : (H ⊓ N).map (QuotientGroup.mk' Z) ≤ N.map (QuotientGroup.mk' Z) :=
    map_mono inf_le_right
  have hcard : (H ⊓ N).relIndex N =
      ((H ⊓ N).map (QuotientGroup.mk' Z)).relIndex (N.map (QuotientGroup.mk' Z)) * Nat.card Z := by
    have h1 := relIndex_mul_card (H := (H ⊓ N).map (QuotientGroup.mk' Z))
      (K := N.map (QuotientGroup.mk' Z))
    have h3 := relIndex_mul_card (H := H ⊓ N) (K := N)
    have h4 := relIndex_mul_card (H := Z) (K := N)
    have h5 : Z.relIndex N = Nat.card (N.map (QuotientGroup.mk' Z)) := by
      rw [← relIndex_bot_left, ← relIndex_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rw [inf_of_le_left hJN, natCard_map_of_isPGroup_of_odd
      (by rw [QuotientGroup.ker_mk']; exact Nat.coprime_two_right.mp hZ) h2] at h1
    rw [inf_of_le_left inf_le_right] at h3
    rw [inf_of_le_left hZN, h5] at h4
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(H ⊓ N))) ?_
    rw [h3, ← h4, ← h1]
    ring
  rw [hJ]
  constructor
  · rintro ⟨-, -, hdvd⟩
    refine ⟨inf_le_right, h2, fun h => hdvd ((hZ.symm.dvd_mul_right).mp ?_)⟩
    change 2 ∣ ((H ⊓ N).map (QuotientGroup.mk' Z)).relIndex (N.map (QuotientGroup.mk' Z)) *
      Nat.card Z
    rw [← hcard]
    exact h
  · rintro ⟨-, -, hdvd⟩
    refine ⟨hJN, h2.map _, fun h => hdvd ?_⟩
    change 2 ∣ (H ⊓ N).relIndex N
    rw [hcard]
    exact dvd_mul_of_dvd_left h _

end Quotient

end CFSG.GroupTheory

end

module

public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

section MulAut

variable {L : Type*} [Group L]

theorem mulAut_mul_conj_eq (φ : MulAut L) (m : L) :
    φ * MulAut.conj m = MulAut.conj (φ m) * φ := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem mulAut_conj_mul_mul_conj_inv (φ : MulAut L) (l : L) :
    MulAut.conj l * φ * (MulAut.conj l)⁻¹ = MulAut.conj (l * (φ l)⁻¹) * φ := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply,
    map_mul, map_inv]

theorem mulAut_conj_range_normal : (MulAut.conj : L →* MulAut L).range.Normal :=
  ⟨fun _ ⟨m, hm⟩ α => MonoidHom.mem_range.2
    ⟨α m, by rw [← hm, mulAut_mul_conj_eq, mul_inv_cancel_right]⟩⟩

theorem mulAut_conj_injective_of_center_eq_bot (hZ : center L = ⊥) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  intro a b h
  have hm : b⁻¹ * a ∈ center L := by
    rw [mem_center_iff]
    intro x
    have hx : a * x * a⁻¹ = b * x * b⁻¹ := by
      simpa only [MulAut.conj_apply] using congrArg (fun φ : MulAut L => φ x) h
    calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [hx]
      _ = b⁻¹ * a * x := by group
  rw [hZ, mem_bot] at hm
  exact (inv_mul_eq_one.1 hm).symm

end MulAut

section Centerless

variable {L : Type} [Group L] [Finite L]

theorem mulAut_eq_one_of_forall_sq_eq_one (hZ : center L = ⊥)
    (hodd : ∀ M : Subgroup L, M.Normal → Odd (Nat.card M) → M = ⊥) {φ : MulAut L}
    (hφφ : φ * φ = 1) (hφ : ∀ l : L, (l * (φ l)⁻¹) ^ 2 = 1 → l * (φ l)⁻¹ = 1) : φ = 1 := by
  classical
  by_contra hne
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hφφl : ∀ l : L, φ (φ l) = l := fun l => by
    rw [← MulAut.mul_apply, hφφ, MulAut.one_apply]
  set I : Subgroup (MulAut L) := (MulAut.conj : L →* MulAut L).range
  have hInorm : I.Normal := mulAut_conj_range_normal
  set X : Subgroup (MulAut L) := I ⊔ zpowers φ
  have hIX : ∀ l : L, MulAut.conj l ∈ X := fun l => mem_sup_left (MonoidHom.mem_range.2 ⟨l, rfl⟩)
  have hφX : φ ∈ X := mem_sup_right (mem_zpowers φ)
  have : Finite (MulAut L) :=
    Finite.of_injective (fun α : MulAut L => (α : L → L)) DFunLike.coe_injective
  have : Fintype X := Fintype.ofFinite X
  set t : X := ⟨φ, hφX⟩
  have ht1 : t ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have ht2 : t * t = 1 := Subtype.ext hφφ
  have hconjX : ∀ g : X, ∃ l : L,
      ((g * t * g⁻¹ : X) : MulAut L) = MulAut.conj (l * (φ l)⁻¹) * φ := by
    rintro ⟨a, ha⟩
    obtain ⟨y, ⟨l, rfl⟩, z, hz, rfl⟩ := mem_sup_of_normal_left.1 ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
    refine ⟨l, ?_⟩
    rw [← mulAut_conj_mul_mul_conj_inv]
    change MulAut.conj l * φ ^ k * φ * (MulAut.conj l * φ ^ k)⁻¹ =
      MulAut.conj l * φ * (MulAut.conj l)⁻¹
    group
  have hisol : ∀ g : X, g * t * g⁻¹ * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    obtain ⟨l, hl⟩ := hconjX g
    generalize hc : g * t * g⁻¹ = c at hg hl ⊢
    have hgc : (c : MulAut L) * φ = φ * c := congrArg Subtype.val hg
    rw [hl] at hgc
    have h1 : MulAut.conj (l * (φ l)⁻¹) * φ = MulAut.conj (φ (l * (φ l)⁻¹)) * φ := by
      rw [← mulAut_mul_conj_eq]
      exact mul_right_cancel (hgc.trans (mul_assoc _ _ _).symm)
    have h2 : l * (φ l)⁻¹ = φ (l * (φ l)⁻¹) := hinj (mul_right_cancel h1)
    have h3 : (l * (φ l)⁻¹) ^ 2 = 1 := by
      calc (l * (φ l)⁻¹) ^ 2 = (l * (φ l)⁻¹) * φ (l * (φ l)⁻¹) := by rw [sq, ← h2]
        _ = 1 := by rw [map_mul, map_inv, hφφl]; group
    apply Subtype.ext
    rw [hl, hφ l h3, map_one, one_mul]
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.ZStar.glauberman_zStar X t ht1 ht2 hisol
  set f : L →* X := (MulAut.conj : L →* MulAut L).codRestrict X hIX
  have hfinj : Function.Injective f := fun a b h => hinj (congrArg Subtype.val h)
  have hM : N.comap f = ⊥ := by
    refine hodd _ (hN.comap f) ?_
    have h1 : Nat.card ((N.comap f).map f) = Nat.card (N.comap f) := card_map_of_injective hfinj
    have h2 : Nat.card ((N.comap f).map f) ∣ Nat.card N := card_dvd_of_le (map_comap_le f N)
    exact Odd.of_dvd_nat hNodd (h1 ▸ h2)
  apply hne
  ext l
  have hmem : l * (φ l)⁻¹ ∈ N.comap f := by
    have hfl : f (l * (φ l)⁻¹) = f l * t * (f l)⁻¹ * t⁻¹ := by
      apply Subtype.ext
      change MulAut.conj (l * (φ l)⁻¹) = MulAut.conj l * φ * (MulAut.conj l)⁻¹ * φ⁻¹
      rw [mulAut_conj_mul_mul_conj_inv, mul_inv_cancel_right]
    change f (l * (φ l)⁻¹) ∈ N
    rw [hfl]
    exact hNt (f l)
  rw [hM, mem_bot] at hmem
  rw [MulAut.one_apply]
  exact (mul_inv_eq_one.1 hmem).symm

theorem foursGroupCondition_of_center_eq_bot (hZ : center L = ⊥)
    (hodd : ∀ M : Subgroup L, M.Normal → Odd (Nat.card M) → M = ⊥) : FoursGroupCondition L := by
  intro φ hφφ hout
  by_contra hcon
  push Not at hcon
  refine hout 1 ?_
  rw [map_one]
  refine mulAut_eq_one_of_forall_sq_eq_one hZ hodd hφφ fun l hl => ?_
  have h := hcon l hl
  rwa [hZ, mem_bot] at h

theorem foursGroupCondition_of_oddCore_eq_bot (hZ : center L = ⊥)
    (hO : standardComponentOddCore L = ⊥) : FoursGroupCondition L :=
  foursGroupCondition_of_center_eq_bot hZ fun _ hM hModd =>
    le_bot_iff.1 (hO ▸ le_sSup ⟨hM, hModd⟩)

theorem foursGroupCondition_of_isSimpleGroup [IsSimpleGroup L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) : FoursGroupCondition L := by
  refine foursGroupCondition_of_center_eq_bot ?_ fun M hM hModd => ?_
  · rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnonab
      have hb : b ∈ center L := by rw [h]; exact mem_top b
      exact absurd (mem_center_iff.1 hb a) hab
  · rcases hM.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, card_top] at hModd
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.2 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hModd) a b)

theorem foursGroupCondition_of_isQuasisimple (hL : CFSG.Open.IsQuasisimple L)
    (hZ : center L = ⊥) : FoursGroupCondition L := by
  have hs : IsSimpleGroup (L ⧸ center L) := hL.2
  have e : L ≃* L ⧸ center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have : IsSimpleGroup L := e.isSimpleGroup
  refine foursGroupCondition_of_isSimpleGroup ?_
  by_contra! hcomm
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  have hxZ : x ∈ center L := mem_center_iff.2 fun g => hcomm g x
  rw [hZ, mem_bot] at hxZ
  exact hx hxZ

end Centerless

section Standard

variable {G : Type} [Group G] [Finite G]

theorem foursGroupCondition_of_isStandard {L : Subgroup G} (hL : standardComponentIsStandard L)
    (hZ : center L = ⊥) : FoursGroupCondition L :=
  foursGroupCondition_of_isQuasisimple hL.1 hZ

theorem card_sylow_eq_two_of_standard_of_center_eq_bot {L : Subgroup G}
    (hset : StandardSetting G L) (hZ : center L = ⊥) (hI : HypothesisOne (L ⧸ center L))
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 :=
  card_sylow_eq_two_of_standard hset hI (foursGroupCondition_of_isStandard hset.standard hZ) S

theorem inf_centralizer_eq_zpowers_of_standard_of_center_eq_bot {L : Subgroup G}
    (hset : StandardSetting G L) (hZ : center L = ⊥) (hI : HypothesisOne (L ⧸ center L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_of_standard hset hI
    (foursGroupCondition_of_isStandard hset.standard hZ) htC ht

end Standard

end CFSG.SeitzReduction

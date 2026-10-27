module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Idx2Q
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocHNLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocHNSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem vPairs_nonempty_of_hsCover_of_mem
    {L K : Subgroup H} {u : H} (hu2 : orderOf u = 2)
    (huL : u ∈ L) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcov : IsHSCover ↥(L ⊓ centralizer ({u} : Set H))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H))))
    (hidx : (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).index = 2)
    (hlt : 11 < (Nat.card L).factorization 2) : (vPairs L K u).Nonempty := by
  set Cu : Subgroup H := L ⊓ centralizer ({u} : Set H) with hCu
  have hKC : K ≤ Cu := fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  set E : Subgroup ↥Cu := K.subgroupOf Cu with hE
  have hKE : E.map Cu.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKC
  have : E.Normal := hcov.normal
  have hZ := hcov.card_center
  obtain ⟨M⟩ := exists_coverModel hcov.perfect hZ hcov.quotient
  obtain ⟨D⟩ := exists_thetaData (E := E) M.toCoverMaps
  have hcardE : Nat.card ↥E = 88704000 := card_eq_of_double_cover hZ hcov.quotient
  have hCuCard : Nat.card ↥Cu = 177408000 := by
    have := Subgroup.card_mul_index E
    rw [hcardE, hidx] at this
    omega
  obtain ⟨P, hTP⟩ := (M.isPGroup_T0.map E.subtype).exists_le_sylow
  let u' : ↥Cu := ⟨u, huL, mem_centralizer_singleton_iff.2 rfl⟩
  have hu'1 : u' ≠ 1 := fun h => by
    have h1 : u = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hu'c : ∀ y : ↥Cu, y * u' = u' * y := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2.2)
  obtain ⟨hu'E, hu'tE⟩ := central_mem_cover hcov M hu'1 hu'c
  have huT : u' ∈ M.T0.map E.subtype :=
    ⟨⟨u', hu'E⟩, by rw [hu'tE]; exact M.tE_mem_T0, rfl⟩
  have huP : u' ∈ (P : Subgroup ↥Cu) := hTP huT
  set S : Subgroup H := (P : Subgroup ↥Cu).map Cu.subtype with hS
  have hSCu : S ≤ Cu := Subgroup.map_subtype_le _
  have hSp : IsPGroup 2 S := P.isPGroup'.map Cu.subtype
  have hScard : Nat.card S = 2 ^ 11 := by
    rw [hS, Subgroup.card_map_of_injective Cu.subtype_injective, P.card_eq_multiplicity, hCuCard,
      factorization_two_177408000']
  have hlt' : Nat.card S < 2 ^ (Nat.card L).factorization 2 := by
    rw [hScard]
    exact Nat.pow_lt_pow_right (by norm_num) hlt
  obtain ⟨T, hTL, hTp, hST⟩ := exists_lt_of_card_lt (hSCu.trans inf_le_left) hSp hlt'
  refine vPairs_nonempty_of_sylow (L := L) (K := K) (S := S) (T := T) hu2 ⟨u', huP, rfl⟩ hSCu ?_ hTL
    hTp hST ?_ ?_ ?_
  · intro S' hS'Cu hS'p hSS'
    have hS'' : IsPGroup 2 (S'.subgroupOf Cu) := hS'p.comap_subtype
    have hPle : (P : Subgroup ↥Cu) ≤ S'.subgroupOf Cu := fun x hx =>
      mem_subgroupOf.2 (hSS' ⟨x, hx, rfl⟩)
    have hPeq : S'.subgroupOf Cu = (P : Subgroup ↥Cu) := P.is_maximal' hS'' hPle
    rw [← Subgroup.map_subgroupOf_eq_of_le hS'Cu, hPeq]
  · rintro _ ⟨c, hcP, rfl⟩ hcomm
    have hc : ∀ y ∈ M.T0.map E.subtype, c * y = y * c := fun y hy =>
      Subtype.ext (hcomm (y : H) ⟨y, hTP hy, rfl⟩)
    have hcE : c ∈ E := D.mem_of_centralizer hcov M hc
    exact (le_sup_left : K ≤ K ⊔ zpowers u) (mem_subgroupOf.1 hcE)
  · intro z hz hzz
    obtain ⟨hzK, hzc⟩ := mem_center_map_iff.1 hz
    have hzC : z ∈ Cu := hKC hzK
    have hzE : (⟨z, hzC⟩ : ↥Cu) ∈ E := mem_subgroupOf.2 hzK
    have hcen : (⟨⟨z, hzC⟩, hzE⟩ : ↥E) ∈ center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subtype.ext (hzc (y : ↥Cu) (mem_subgroupOf.1 y.2)).symm)
    rcases (M.mem_center_iff hZ).1 hcen with h | h
    · left
      exact congrArg (fun w : ↥E => ((w : ↥Cu) : H)) h
    · right
      have h' := hu'tE.trans h.symm
      exact (congrArg (fun w : ↥E => ((w : ↥Cu) : H)) h').symm
  · have hinf := inf_eq_map_T0 M hcardE P.isPGroup' hTP
    have hSK : S ⊓ K = (M.T0.map E.subtype).map Cu.subtype := by
      rw [← hinf, Subgroup.map_inf _ _ _ Cu.subtype_injective, hKE]
    have h1 : Nat.card ↥(S ⊓ K) = 2 ^ 10 := by
      rw [hSK, Subgroup.card_map_of_injective Cu.subtype_injective,
        Subgroup.card_map_of_injective E.subtype_injective, M.card_T0]
      norm_num
    have h2 : Nat.card ↥K = 88704000 := by
      rw [← hKE, Subgroup.card_map_of_injective Cu.subtype_injective]
      exact hcardE
    unfold twoAdic
    rw [h1, h2, factorization_two_card_E, Nat.Prime.factorization_pow Nat.prime_two]
    simp

theorem sol78Local39Q_of_hsCover
    {N L K : Subgroup H} {t u : H}
    (hset : SolomonSettingQ H N L K t u) (huL : u ∈ L)
    (hcov : IsHSCover ↥(L ⊓ centralizer ({u} : Set H))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H))))
    (hidx : (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).index = 2)
    (hlt : 11 < (Nat.card L).factorization 2)
    (hov : ∀ X : Subgroup H, K ≤ X → X ≤ L → X ≤ L ⊓ centralizer ({u} : Set H) ∨ X = L) :
    (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u := by
  have hKC : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
    ⟨hset.K_le hk, mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hset.u_mem_centralizer_K k hk)⟩
  obtain ⟨-, hC⟩ := central_eq_of_hsCover huL hset.u_order hcov
  refine ⟨vPairs_nonempty_of_hsCover_of_mem hset.u_order huL hset.K_le
    (fun k hk => mem_centralizer_iff.1 hset.u_mem_centralizer_K k hk) hcov hidx hlt, ?_,
    sol78Generate_of_overgroups hset.u_order hC hset.K_le huL hov⟩
  refine sol78Fusion39_of_induced
    (fun k hk => mem_centralizer_iff.1 hset.u_mem_centralizer_K k hk) ?_
    (inducedByCentralizer_of_hsCover hKC hcov hidx)
  intro g hg
  obtain ⟨-, hKg⟩ := map_conj_eq_of_hyp35 hset.hyp35 hg
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => conj_mem_of_map_eq hKg hh, fun hh => ?_⟩
  have := conj_inv_mem_of_map_eq hKg hh
  simpa [mul_assoc] using this

theorem solomonLocalQ_of_hsCover
    {s : TauCeti.SporadicName} {L K : Subgroup H} {u : H} (hL : OddCover s L) (hout : OutTwo ↥L)
    (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcov : IsHSCover ↥(L ⊓ centralizer ({u} : Set H))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H)))) : SolomonLocalQ L K u := by
  have hq := (isComponent_of_isHSCover hcov).1
  exact solomonLocalQ_of_normal_quasisimple hL hout huL hu2 hKL hKu
    (central_eq_of_hsCover huL hu2 hcov).2 hcov.normal ⟨hq.1.commutator_eq_top, hq.2.1⟩

end CFSG.EvenSporadicStandard.Induction

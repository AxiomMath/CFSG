module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Section
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Cover

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

@[expose] def secStd (Q P : Subgroup H) {s : H} (hs : s ∈ normalizer (Q : Set H)) :
    Subgroup ↥(secGrp Q hs) :=
  (P.subgroupOf (Q ⊔ zpowers s)).map (secPre Q hs).rangeRestrict

variable (Q P : Subgroup H) {s : H} (hs : s ∈ normalizer (Q : Set H))

omit [Finite H] in
include hs in
theorem sup_le_normalizer : Q ⊔ zpowers s ≤ normalizer (Q : Set H) :=
  sup_le Subgroup.le_normalizer (by rw [zpowers_le]; exact hs)

omit [Finite H] in
include hs in
theorem rangeRestrict_eq_one_iff (x : ↥(Q ⊔ zpowers s)) :
    (secPre Q hs).rangeRestrict x = 1 ↔ (x : H) ∈ centralizer (Q : Set H) := by
  rw [← secPre_eq_one_iff Q hs x]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

include hs in
theorem secStd_stdBare (hPQ : P ≤ Q)
    (hstd : StdModulo (Q ⊔ zpowers s) (centralizer (Q : Set H)) P) :
    StdBare (secStd Q P hs) := by
  obtain ⟨hZ, hstdq⟩ := hstd
  have hXN := sup_le_normalizer Q hs
  have : ((centralizer (Q : Set H)).subgroupOf (Q ⊔ zpowers s)).Normal := hZ
  set Z' := (centralizer (Q : Set H)).subgroupOf (Q ⊔ zpowers s) with hZ'
  let ρ : ↥(Q ⊔ zpowers s) →* ↥(secGrp Q hs) := (secPre Q hs).rangeRestrict
  have hcen : ∀ x : ↥(Q ⊔ zpowers s), x ∈ Z' → (x : H) ∈ centralizer (Q : Set H) := fun x hx => hx
  have hker : Z' ≤ ρ.ker := fun x hx =>
    (rangeRestrict_eq_one_iff Q hs x).2 (hcen x hx)
  let θ : ↥(Q ⊔ zpowers s) ⧸ Z' →* ↥(secGrp Q hs) := QuotientGroup.lift Z' ρ hker
  have hρsurj : Function.Surjective ρ := (secPre Q hs).rangeRestrict_surjective
  have hθ : Function.Surjective θ := by
    intro y
    obtain ⟨x, rfl⟩ := hρsurj y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hQn : (Q.subgroupOf (Q ⊔ zpowers s)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hXN
  set M : Subgroup (↥(Q ⊔ zpowers s) ⧸ Z') :=
    (Q.subgroupOf (Q ⊔ zpowers s)).map (QuotientGroup.mk' Z') with hM
  have hMn : M.Normal := Subgroup.Normal.map hQn _ (QuotientGroup.mk'_surjective Z')
  have hPM : (P.subgroupOf (Q ⊔ zpowers s)).map (QuotientGroup.mk' Z') ≤ M :=
    Subgroup.map_mono fun x hx => hPQ hx
  have hC1 : θ.ker ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, ⟨x, hx, rfl⟩⟩
    have h1 : ρ x = 1 := hy1
    have h2 := (rangeRestrict_eq_one_iff Q hs x).1 h1
    have hxQ : (x : H) ∈ Q := hx
    have hxz : x ∈ Z' := h2
    exact (QuotientGroup.eq_one_iff x).2 hxz
  have hC2 : θ.ker ≤ centralizer (M : Set (↥(Q ⊔ zpowers s) ⧸ Z')) := by
    intro y hy
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective y
    have h2 := (rangeRestrict_eq_one_iff Q hs x₀).1 hy
    rw [mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    show QuotientGroup.mk q * QuotientGroup.mk x₀ = QuotientGroup.mk x₀ * QuotientGroup.mk q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.1 h2 (q : H) hq).symm.symm)
  have key := stdBare_map_of_surj θ hθ hPM hC1 hC2 hstdq
  have heq : ((P.subgroupOf (Q ⊔ zpowers s)).map (QuotientGroup.mk' Z')).map θ =
      secStd Q P hs := by
    rw [Subgroup.map_map]
    rfl
  rw [← heq]
  exact key

omit [Finite H] in
@[expose] def secStdHom (hPQ : P ≤ Q) : ↥P →* ↥(secStd Q P hs) :=
  ((secPre Q hs).rangeRestrict.comp (Subgroup.inclusion (hPQ.trans le_sup_left))).codRestrict
    (secStd Q P hs) (fun x => ⟨Subgroup.inclusion (hPQ.trans le_sup_left) x, x.2, rfl⟩)

omit [Finite H] in
include hs in
theorem secStdHom_surjective (hPQ : P ≤ Q) : Function.Surjective (secStdHom Q P hs hPQ) := by
  intro z
  obtain ⟨y, hy, hyz⟩ := z.2
  refine ⟨⟨(y : H), hy⟩, Subtype.ext ?_⟩
  show (secPre Q hs).rangeRestrict (Subgroup.inclusion (hPQ.trans le_sup_left) ⟨(y : H), hy⟩) =
    (z : ↥(secGrp Q hs))
  rw [← hyz]
  rfl

omit [Finite H] in
include hs in
theorem secStdHom_ker_le (hPQ : P ≤ Q) : (secStdHom Q P hs hPQ).ker ≤ center ↥P := by
  intro x hx
  have h1 : (secPre Q hs).rangeRestrict (Subgroup.inclusion (hPQ.trans le_sup_left) x) = 1 :=
    congrArg Subtype.val hx
  have h2 := (rangeRestrict_eq_one_iff Q hs _).1 h1
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (mem_centralizer_iff.1 h2 (g : H) (hPQ g.2))

omit [Finite H] in
include hs in
theorem secStd_quasisimple (hPQ : P ≤ Q) (hPq : CFSG.IsQuasisimple ↥P) :
    CFSG.IsQuasisimple ↥(secStd Q P hs) :=
  isQuasisimple_of_cover hPq (secStdHom Q P hs hPQ) (secStdHom_surjective Q P hs hPQ)
    (secStdHom_ker_le Q P hs hPQ)

omit [Finite H] in
include hs in
theorem secStd_cqEquiv (hPQ : P ≤ Q) (hPq : CFSG.IsQuasisimple ↥P) :
    Nonempty ((↥P ⧸ center ↥P) ≃* (↥(secStd Q P hs) ⧸ center ↥(secStd Q P hs))) := by
  have := hPq.1
  exact cqEquiv_of_cover (secStdHom Q P hs hPQ) (secStdHom_surjective Q P hs hPQ)
    (secStdHom_ker_le Q P hs hPQ)

include hs in
theorem secStd_solStd (hPQ : P ≤ Q) (hPq : CFSG.IsQuasisimple ↥P)
    (hstd : StdBare (secStd Q P hs)) (hs2 : s ^ 2 ∈ centralizer (Q : Set H))
    (hsQ : s ∉ centralizer (Q : Set H)) (hsP : s ∈ centralizer (P : Set H)) :
    SolStd (secStd Q P hs) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let xs : ↥(Q ⊔ zpowers s) := ⟨s, mem_sup_right (mem_zpowers s)⟩
  let t : ↥(secGrp Q hs) := (secPre Q hs).rangeRestrict xs
  have ht1 : t * t = 1 := by
    apply Subtype.ext
    show secPre Q hs xs * secPre Q hs xs = 1
    rw [← map_mul]
    exact (secPre_eq_one_iff Q hs _).2 (by simpa [xs, sq] using hs2)
  have ht2 : orderOf t = 2 := by
    refine orderOf_eq_prime (by rw [sq]; exact ht1) ?_
    intro h
    exact hsQ ((rangeRestrict_eq_one_iff Q hs xs).1 h)
  have htL : t ∈ centralizer ((secStd Q P hs : Subgroup ↥(secGrp Q hs)) : Set ↥(secGrp Q hs)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    show (secPre Q hs).rangeRestrict y * (secPre Q hs).rangeRestrict xs =
      (secPre Q hs).rangeRestrict xs * (secPre Q hs).rangeRestrict y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 hsP (y : H) hy)
  exact solStd_of_stdBare_of_involution hstd (secStd_quasisimple Q P hs hPQ hPq) ht2 htL

end CFSG.EvenSporadicStandard.Induction.Hyp

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiLocal39

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78

structure CentralizerModel (Y : Type) [Group Y] [Finite Y] (uY : Y) : Prop where
  squareFacts : ∃ (S : Subgroup Y) (d : Y), SquareFacts (centralizer ({uY} : Set Y)) S uY d
  coatom : IsCoatom (centralizer ({uY} : Set Y))
  twoAdic_lt : twoAdic (centralizer ({uY} : Set Y)) < twoAdic (⊤ : Subgroup Y)
  stdBare : StdBare (centralizer ({uY} : Set Y))
  card_centralizer : Nat.card (centralizer (centralizer ({uY} : Set Y) : Set Y)) ≤ 2
  outTwo : OutTwo Y

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

omit [Finite H] in
theorem commutator_subgroupOf_eq_self (hKL : K ≤ L) (hq : CFSG.IsQuasisimple ↥K) :
    ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L := by
  have hp : Group.IsPerfect ↥K := hq.1
  have : Group.IsPerfect ↥(K.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKL).symm.surjective
  exact Cover.commutator_eq_self_of_isPerfect this

omit [Finite H] in
theorem map_subtype_map_conj (K' : Subgroup ↥L) (g : ↥L) :
    (K'.map (MulAut.conj g).toMonoidHom).map L.subtype =
      (K'.map L.subtype).map (MulAut.conj (g : H)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1


omit [Finite H] in
theorem sq_of_orderOf_two {u : H} (huL : u ∈ L) (hu2 : orderOf u = 2) :
    (⟨u, huL⟩ : ↥L) * ⟨u, huL⟩ = 1 :=
  Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hu2)

omit [Finite H] in
theorem central_subgroupOf {u : H} (huL : u ∈ L) (hKu : ∀ k ∈ K, k * u = u * k) :
    ∀ k ∈ K.subgroupOf L, k * (⟨u, huL⟩ : ↥L) = ⟨u, huL⟩ * k := fun _ hk =>
  Subtype.ext (hKu _ (Subgroup.mem_subgroupOf.1 hk))

theorem solomonLocalQ_of_cover (hL : CFSG.IsQuasisimple ↥L)
    (hodd : Odd (Nat.card (center ↥L))) (hKq : CFSG.IsQuasisimple ↥K)
    (huL : u ∈ L) (hnc : u ∉ centralizer (L : Set H)) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k)
    (hmodel : CentralizerModel (↥L ⧸ center ↥L) ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L))
    (hbar : bar (K.subgroupOf L) =
      centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) :
    SolomonLocalQ L K u := by
  have hu1 := sq_of_orderOf_two huL hu2
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  have hKu' := central_subgroupOf huL hKu
  refine
  { u_order := hu2
    u_mem := Subgroup.le_normalizer huL
    u_not_central := hnc
    K_le := hKL
    u_mem_centralizer_K := mem_centralizer_iff.2 hKu
    standard_in_L := ?_
    autCentralizer_two := ?_ }
  · refine ⟨stdBare_of_bar hodd hK' (by rw [hbar]; exact hmodel.stdBare),
      ⟨u, huL⟩, by rw [Subgroup.orderOf_mk]; exact hu2, ?_⟩
    have hle : K.subgroupOf L ≤ centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L) := fun k hk =>
      mem_centralizer_singleton_iff.2 (hKu' k hk)
    have hqK : CFSG.IsQuasisimple ↥(K.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL).symm hKq
    have hC : centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L) ≤ normalizer (K.subgroupOf L : Set ↥L) := by
      rw [centralizer_singleton_eq_sup hodd hu1 hKu' hbar]
      exact sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer _)
    exact isCompIn_of_normal hle hqK ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hC)
  · exact twoAdic_autCentralizer_le_of_cover hL.1 hmodel.outTwo
      (by rw [hbar]; exact hmodel.card_centralizer)


theorem local39_of_cover (hL : CFSG.IsQuasisimple ↥L) (hodd : Odd (Nat.card (center ↥L)))
    (hKq : CFSG.IsQuasisimple ↥K) (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (h35 : K = componentProduct K u)
    (hmodel : CentralizerModel (↥L ⧸ center ↥L) ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L))
    (hbar : bar (K.subgroupOf L) =
      centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) :
    (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u := by
  have hu1 := sq_of_orderOf_two huL hu2
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  have hKu' := central_subgroupOf huL hKu
  have hKcen : u ∈ centralizer (K : Set H) := mem_centralizer_iff.2 hKu
  have hX : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    have := Group.isPerfect_def.1 hL.1
    rwa [_root_.commutator_def] at this
  obtain ⟨Sb, db, hSq⟩ := hmodel.squareFacts
  rw [← hbar] at hSq
  obtain ⟨S', d', hSq'⟩ := exists_squareFacts_of_bar hodd hu1 hKu' hSq
  have hSqH := hSq'.map L.subtype L.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hKL] at hSqH
  have hKC : ∀ S'' : Subgroup H, S'' ≤ L ⊓ centralizer ({u} : Set H) → IsPGroup 2 S'' →
      S'' ≤ K := by
    intro S'' hle hp x hx
    have hT : IsPGroup 2 (S''.subgroupOf L) := hp.comap_subtype
    have hTle : S''.subgroupOf L ≤ K.subgroupOf L ⊔ center ↥L := by
      intro y hy
      rw [← centralizer_singleton_eq_sup hodd hu1 hKu' hbar]
      refine mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
      exact mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_subgroupOf.1 hy)).2
    have := le_of_isPGroup_le_sup_central (le_refl (center ↥L)) hodd hT hTle
    have hxL : x ∈ L := (hle hx).1
    have h1 : (⟨x, hxL⟩ : ↥L) ∈ S''.subgroupOf L := hx
    exact Subgroup.mem_subgroupOf.1 (this h1)
  have hgen : ∀ l ∈ L, K.map (conjHom l) ≠ K → K ⊔ K.map (conjHom l) = L := by
    intro l hl hne
    have hne' : (K.subgroupOf L).map (MulAut.conj (⟨l, hl⟩ : ↥L)).toMonoidHom ≠
        K.subgroupOf L := by
      intro heq
      apply hne
      have := congrArg (Subgroup.map L.subtype) heq
      rw [map_subtype_map_conj, Subgroup.map_subgroupOf_eq_of_le hKL] at this
      exact this
    have hgenY : ∀ y : ↥L ⧸ center ↥L,
        (bar (K.subgroupOf L)).map (MulAut.conj y).toMonoidHom ≠ bar (K.subgroupOf L) →
          bar (K.subgroupOf L) ⊔ (bar (K.subgroupOf L)).map (MulAut.conj y).toMonoidHom =
            (⊤ : Subgroup (↥L ⧸ center ↥L)) := by
      intro y hy
      rw [hbar] at hy ⊢
      set KY : Subgroup (↥L ⧸ center ↥L) :=
        centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L)) with hKY
      have hco : IsCoatom KY := hmodel.coatom
      rcases hco.le_iff.1 (le_sup_left : KY ≤ KY ⊔ KY.map (MulAut.conj y).toMonoidHom) with h | h
      · exact h
      · exfalso
        apply hy
        have hle2 : KY.map (MulAut.conj y).toMonoidHom ≤ KY :=
          calc KY.map (MulAut.conj y).toMonoidHom ≤ KY ⊔ KY.map (MulAut.conj y).toMonoidHom :=
                le_sup_right
            _ = KY := h
        exact Subgroup.eq_of_le_of_card_ge hle2
          (by rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
    have htop := sup_conj_eq_top hK' hX hgenY hne'
    have := congrArg (Subgroup.map L.subtype) htop
    rw [Subgroup.map_sup, map_subtype_map_conj, Subgroup.map_subgroupOf_eq_of_le hKL,
      Subgroup.map_top, Subgroup.range_subtype] at this
    exact this
  have hlt : twoAdic K < twoAdic L := by
    have e1 : twoAdic K = twoAdic (K.subgroupOf L) := by
      unfold twoAdic
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
    have e2 : twoAdic (K.subgroupOf L) = twoAdic (bar (K.subgroupOf L)) :=
      (twoAdic_bar hodd _).symm
    have e3 : twoAdic (⊤ : Subgroup (↥L ⧸ center ↥L)) = twoAdic L := by
      have h1 := twoAdic_bar hodd (⊤ : Subgroup ↥L)
      have hb : bar (⊤ : Subgroup ↥L) = (⊤ : Subgroup (↥L ⧸ center ↥L)) := by
        unfold bar
        rw [Subgroup.map_top, MonoidHom.range_eq_top]
        exact QuotientGroup.mk_surjective
      rw [hb] at h1
      rw [h1]
      unfold twoAdic
      rw [Subgroup.card_top]
    rw [e1, e2, hbar, ← e3]
    exact hmodel.twoAdic_lt
  exact sol78Local39Q_of_squareFacts hu2 hKL hKcen h35 hKC hgen hlt hSqH

end CFSG.EvenSporadicStandard.Induction

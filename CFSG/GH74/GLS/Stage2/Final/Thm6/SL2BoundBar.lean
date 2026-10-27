module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Local
open scoped Pointwise

section Basic

variable {G : Type} [Group G] {z : G}

theorem bar_mem_barOf_iff {X : Subgroup G} {y : CentralizerBar z} :
    y ∈ barOf z X ↔ ∃ (x : G) (hx : x ∈ Cen z), x ∈ X ∧ toBar z ⟨x, hx⟩ = y := by
  unfold barOf
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨x, hx⟩, hxX, rfl⟩
    exact ⟨x, hx, hxX, rfl⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hx⟩, hxX, rfl⟩

theorem bar_mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g * (MulAut.conj g⁻¹).toMonoidHom y * g⁻¹ = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this]
    exact hy
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group

theorem bar_mem_normalizer_iff_conjugate_eq {H : Subgroup G} {g : G} :
    g ∈ normalizer (H : Set G) ↔ conjugate H g = H := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    ext x
    rw [bar_mem_conjugate_iff]
    exact (h x).symm
  · intro h x
    have := Subgroup.ext_iff.1 h x
    rw [bar_mem_conjugate_iff] at this
    exact this.symm

theorem bar_isComponent_conjugate {H : Subgroup G} (hH : IsComponent H) (g : G) :
    IsComponent (conjugate H g) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) hH

end Basic

section S1

variable {G : Type} [Group G] {z : G}

theorem bar_mem_S1_iff {S : Subgroup G} {s : G} :
    s ∈ S1 S z ↔ s ∈ S ∧ ∃ hs : s ∈ Cen z, ∀ K : Subgroup (CentralizerBar z),
      IsComponent K → K ≤ LBar z → toBar z ⟨s, hs⟩ ∈ normalizer (K : Set (CentralizerBar z)) := by
  unfold S1
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hsS, ⟨c, hc, rfl⟩⟩
    refine ⟨hsS, c.2, fun K hK hKL => ?_⟩
    simp only [Subgroup.mem_iInf, Set.mem_ofPred_eq, Subgroup.mem_comap] at hc
    exact hc K ⟨hK, hKL⟩
  · rintro ⟨hsS, hs, h⟩
    refine ⟨hsS, ⟨⟨s, hs⟩, ?_, rfl⟩⟩
    simp only [Subgroup.mem_iInf, Set.mem_ofPred_eq, Subgroup.mem_comap]
    exact fun K hK => h K hK.1 hK.2

theorem bar_S1_le_S {S : Subgroup G} : S1 S z ≤ S := inf_le_left

@[expose] def barS1With (S : Subgroup G) (z : G) (B : Subgroup (CentralizerBar z)) : Subgroup G :=
  S1 S z ⊓ (B.comap (toBar z)).map (Cen z).subtype

theorem bar_mem_S1With_iff {S : Subgroup G} {B : Subgroup (CentralizerBar z)} {s : G} :
    s ∈ barS1With S z B ↔ s ∈ S1 S z ∧ ∃ hs : s ∈ Cen z, toBar z ⟨s, hs⟩ ∈ B := by
  unfold barS1With
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨h1, ⟨c, hc, rfl⟩⟩
    exact ⟨h1, c.2, hc⟩
  · rintro ⟨h1, hs, hB⟩
    exact ⟨h1, ⟨⟨s, hs⟩, hB, rfl⟩⟩

theorem bar_S1With_le_S1 {S : Subgroup G} {B : Subgroup (CentralizerBar z)} :
    barS1With S z B ≤ S1 S z :=
  inf_le_left

end S1

section Bar

variable {H : Type} [Group H]

theorem bar_le_centralizer_of_comm {L L' : Subgroup H} (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) :
    L' ≤ centralizer (L : Set H) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact hcomm a ha b hb

theorem bar_sup_le_normalizer_inf {L L' : Subgroup H} (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) :
    L ⊔ L' ≤ normalizer (L : Set H) ⊓ normalizer (L' : Set H) := by
  have h1 : L' ≤ normalizer (L : Set H) :=
    (bar_le_centralizer_of_comm hcomm).trans (Subgroup.centralizer_le_normalizer _)
  have h2 : L ≤ normalizer (L' : Set H) :=
    (bar_le_centralizer_of_comm (fun b hb a ha => (hcomm a ha b hb).symm)).trans
      (Subgroup.centralizer_le_normalizer _)
  exact sup_le (le_inf Subgroup.le_normalizer h2) (le_inf h1 Subgroup.le_normalizer)

theorem bar_mem_normalizer_other {L L' : Subgroup H} (hne : L ≠ L')
    (hcomps : {K : Subgroup H | IsComponent K} = {L, L'}) {x : H}
    (hx : x ∈ normalizer (L : Set H)) : x ∈ normalizer (L' : Set H) := by
  have hL' : IsComponent L' := by
    have : L' ∈ ({L, L'} : Set (Subgroup H)) := Set.mem_insert_of_mem _ rfl
    rw [← hcomps] at this
    exact this
  have hmem : conjugate L' x ∈ ({L, L'} : Set (Subgroup H)) := by
    rw [← hcomps]
    exact bar_isComponent_conjugate hL' x
  rw [bar_mem_normalizer_iff_conjugate_eq] at hx ⊢
  rcases hmem with h | h
  · exfalso
    apply hne
    have : conjugate L' x = conjugate L x := h.trans hx.symm
    exact (Subgroup.map_injective (MulAut.conj x⁻¹).injective this).symm
  · exact h

theorem bar_mem_normalizer_comp {L L' : Subgroup H}
    (hcomps : {K : Subgroup H | IsComponent K} = {L, L'}) {x : H}
    (hxL : x ∈ normalizer (L : Set H)) (hxL' : x ∈ normalizer (L' : Set H))
    {K : Subgroup H} (hK : IsComponent K) : x ∈ normalizer (K : Set H) := by
  have : K ∈ ({L, L'} : Set (Subgroup H)) := by
    rw [← hcomps]
    exact hK
  rcases this with rfl | rfl
  · exact hxL
  · exact hxL'

theorem bar_isCentralProd_symm {A B Y : Subgroup H} (h : IsCentralProd A B Y) :
    IsCentralProd B A Y :=
  ⟨(sup_comm _ _).trans h.1, fun b hb a ha => (h.2.1 a ha b hb).symm, by rw [inf_comm]; exact h.2.2⟩

theorem bar_not_le_sup_centralizer [Finite H] (L A : Subgroup H)
    (hcard : Nat.card L =
      Nat.card (↥(L ⊔ A) ⧸ (centralizer (L : Set H)).subgroupOf (L ⊔ A)))
    (hc : ∃ c ∈ L, c ≠ 1 ∧ c ∈ centralizer (L : Set H)) :
    ¬ A ≤ L ⊔ centralizer (L : Set H) := by
  intro hA
  obtain ⟨c, hcL, hc1, hcC⟩ := hc
  have hLY : L ≤ L ⊔ A := le_sup_left
  have hYle : L ⊔ A ≤ L ⊔ centralizer (L : Set H) := sup_le le_sup_left hA
  let f : L → ↥(L ⊔ A) ⧸ (centralizer (L : Set H)).subgroupOf (L ⊔ A) :=
    fun l => QuotientGroup.mk ⟨l.1, hLY l.2⟩
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : H) ∈ L ⊔ centralizer (L : Set H) := hYle y.2
      have hmul := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set H))
        (Subgroup.centralizer_le_normalizer _)
      have hy' : (y : H) ∈ (L : Set H) * (centralizer (L : Set H) : Set H) := by
        rw [← hmul]
        exact hy
      obtain ⟨l, hl, d, hd, hld⟩ := Set.mem_mul.1 hy'
      refine ⟨⟨l, hl⟩, ?_⟩
      show (QuotientGroup.mk ⟨l, hLY hl⟩ : ↥(L ⊔ A) ⧸ _) = QuotientGroup.mk y
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show l⁻¹ * (y : H) ∈ centralizer (L : Set H)
      have : l⁻¹ * (y : H) = d := by
        rw [← hld]
        group
      rw [this]
      exact hd
  have hbij : Function.Bijective f := hsurj.bijective_of_nat_card_le (le_of_eq hcard)
  have hfc : f ⟨c, hcL⟩ = f 1 := by
    show (QuotientGroup.mk ⟨c, hLY hcL⟩ : ↥(L ⊔ A) ⧸ _) = QuotientGroup.mk ⟨1, hLY (one_mem L)⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show c⁻¹ * 1 ∈ centralizer (L : Set H)
    simpa using (centralizer (L : Set H)).inv_mem hcC
  have := hbij.1 hfc
  exact hc1 (congrArg Subtype.val this)

theorem bar_card_eq_of_pgl (L A : Subgroup H) {q : ℕ}
    (hsl : HasSL2Model ↥L (fun r => r = q)) (hpgl : InducedPGL2 L A q) :
    Nat.card L = Nat.card (↥(L ⊔ A) ⧸ (centralizer (L : Set H)).subgroupOf (L ⊔ A)) := by
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := hsl
  obtain ⟨hN, F₀, hF₀, hFin₀, hF₀q, ⟨e₀⟩⟩ := hpgl
  rw [Nat.card_congr e.toEquiv, Nat.card_congr e₀.toEquiv,
    CFSG.GorensteinWalter.pgl2_card_formula, hF₀q,
    ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFq]

end Bar

section Main

variable {G : Type} [Group G] [Finite G] {z : G}

theorem bar_not_SBar_le {S : Subgroup G} {q : ℕ} {L L' : Subgroup (CentralizerBar z)}
    (hprod : IsCentralProd L L' (LBar z)) (hsl : HasSL2Model ↥L (fun r => r = q))
    (hpgl : InducedPGL2 L (SBar (S1 S z) z) q) :
    ¬ SBar (S1 S z) z ≤ L ⊔ centralizer (L : Set (CentralizerBar z)) := by
  refine bar_not_le_sup_centralizer L (SBar (S1 S z) z) (bar_card_eq_of_pgl L _ hsl hpgl) ?_
  obtain ⟨-, hcomm, hcard⟩ := hprod
  have h1 : 1 < Nat.card ↥(L ⊓ L') := by
    rw [hcard]
    norm_num
  have : Nontrivial ↥(L ⊓ L') := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨c, hc⟩ := exists_ne (1 : ↥(L ⊓ L'))
  have hcL : (c : CentralizerBar z) ∈ L ∧ (c : CentralizerBar z) ∈ L' := Subgroup.mem_inf.1 c.2
  exact ⟨c, hcL.1, fun h => hc (Subtype.ext h), bar_le_centralizer_of_comm hcomm hcL.2⟩

theorem bar_relIndex_ne_zero (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  have : H.IsFiniteRelIndex K := Subgroup.isFiniteRelIndex_of_finiteIndex
  exact Subgroup.relIndex_ne_zero

theorem inner_mem_LC_bar {S : Subgroup G} {q : ℕ} {L L' : Subgroup (CentralizerBar z)}
    (hSC : S ≤ Cen z) (hne : L ≠ L') (hprod : IsCentralProd L L' (LBar z))
    (hcomps : {K : Subgroup (CentralizerBar z) | IsComponent K} = {L, L'})
    (hsl : HasSL2Model ↥L (fun r => r = q)) (hpgl : InducedPGL2 L (SBar (S1 S z) z) q)
    (hswap : ∃ s ∈ S, Swaps z s L L') (hidx : (RC S z).relIndex S ≤ 4)
    {t : G} (htS : t ∈ S) (htC : t ∈ Cen z)
    (hnorm : toBar z ⟨t, htC⟩ ∈ normalizer (L : Set (CentralizerBar z)))
    (hinn : toBar z ⟨t, htC⟩ ∈ L ⊔ centralizer (L : Set (CentralizerBar z))) : t ∈ LC z := by
  have hsup : L ⊔ L' = LBar z := hprod.1
  have hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := hprod.2.1
  have hLcomp : IsComponent L := by
    have : L ∈ ({L, L'} : Set (Subgroup (CentralizerBar z))) := Set.mem_insert _ _
    rw [← hcomps] at this
    exact this
  set T : Subgroup G := barS1With S z (L ⊔ centralizer (L : Set (CentralizerBar z))) with hT
  have htT : t ∈ T := by
    rw [hT, bar_mem_S1With_iff]
    refine ⟨?_, htC, hinn⟩
    rw [bar_mem_S1_iff]
    exact ⟨htS, htC, fun K hK _ =>
      bar_mem_normalizer_comp hcomps hnorm (bar_mem_normalizer_other hne hcomps hnorm) hK⟩
  have hRT : RC S z ≤ T := by
    intro s hs
    have hs' : s ∈ S ⊓ LC z := hs
    have hsC : s ∈ Cen z := hSC hs'.1
    have hsL : toBar z ⟨s, hsC⟩ ∈ LBar z := bar_mem_barOf_iff.2 ⟨s, hsC, hs'.2, rfl⟩
    rw [← hsup] at hsL
    have hsN := bar_sup_le_normalizer_inf hcomm hsL
    rw [hT, bar_mem_S1With_iff]
    refine ⟨?_, hsC, ?_⟩
    · rw [bar_mem_S1_iff]
      exact ⟨hs'.1, hsC, fun K hK _ => bar_mem_normalizer_comp hcomps hsN.1 hsN.2 hK⟩
    · exact (sup_le le_sup_left ((bar_le_centralizer_of_comm hcomm).trans le_sup_right)) hsL
  have hS₁S : S1 S z ≤ S := bar_S1_le_S
  have hTS₁ : T ≤ S1 S z := bar_S1With_le_S1
  have hRS₁ : RC S z ≤ S1 S z := hRT.trans hTS₁
  have hnS : ¬ S ≤ S1 S z := by
    intro hle
    obtain ⟨s, hsS, hsC, h1, -⟩ := hswap
    obtain ⟨hs, hK⟩ := (bar_mem_S1_iff.1 (hle hsS)).2
    have hLle : L ≤ LBar z := hsup ▸ le_sup_left
    have h2 := hK L hLcomp hLle
    rw [bar_mem_normalizer_iff_conjugate_eq] at h2
    exact hne (h2.symm.trans h1)
  have hnT : ¬ S1 S z ≤ T := by
    intro hle
    refine bar_not_SBar_le hprod hsl hpgl fun y hy => ?_
    obtain ⟨x, hx, hxS1, rfl⟩ := bar_mem_barOf_iff.1 hy
    obtain ⟨-, hx', hxY⟩ := bar_mem_S1With_iff.1 (hle hxS1)
    exact hxY
  have e1 := Subgroup.relIndex_mul_relIndex (RC S z) T (S1 S z) hRT hTS₁
  have e2 := Subgroup.relIndex_mul_relIndex (RC S z) (S1 S z) S hRS₁ hS₁S
  have hb : 2 ≤ T.relIndex (S1 S z) := by
    have h0 : T.relIndex (S1 S z) ≠ 0 := bar_relIndex_ne_zero _ _
    have h1 : T.relIndex (S1 S z) ≠ 1 := fun h => hnT (Subgroup.relIndex_eq_one.1 h)
    omega
  have hc : 2 ≤ (S1 S z).relIndex S := by
    have h0 : (S1 S z).relIndex S ≠ 0 := bar_relIndex_ne_zero _ _
    have h1 : (S1 S z).relIndex S ≠ 1 := fun h => hnS (Subgroup.relIndex_eq_one.1 h)
    omega
  have ha0 : (RC S z).relIndex T ≠ 0 := bar_relIndex_ne_zero _ _
  have ha : (RC S z).relIndex T = 1 := by
    by_contra hne1
    have h2 : 2 ≤ (RC S z).relIndex T := by omega
    have h8 : 2 * 2 * 2 ≤ (RC S z).relIndex S := by
      rw [← e2, ← e1]
      exact Nat.mul_le_mul (Nat.mul_le_mul h2 hb) hc
    omega
  have hTR : T ≤ RC S z := Subgroup.relIndex_eq_one.1 ha
  have := hTR htT
  exact (this : t ∈ S ⊓ LC z).2

end Main

section KLevel

variable {G : Type} [Group G] {z : G}

theorem bar_mem_normalizer_image {K : Subgroup G} {t : G} (htC : t ∈ Cen z)
    (htN : t ∈ normalizer (K : Set G)) :
    toBar z ⟨t, htC⟩ ∈ normalizer (barOf z K : Set (CentralizerBar z)) := by
  have key : ∀ {w : G} (hwC : w ∈ Cen z), w ∈ normalizer (K : Set G) →
      ∀ {l : CentralizerBar z}, l ∈ barOf z K →
        toBar z ⟨w, hwC⟩ * l * (toBar z ⟨w, hwC⟩)⁻¹ ∈ barOf z K := by
    intro w hwC hwN l hl
    obtain ⟨x, hx, hxK, rfl⟩ := bar_mem_barOf_iff.1 hl
    refine bar_mem_barOf_iff.2 ⟨w * x * w⁻¹,
      (Cen z).mul_mem ((Cen z).mul_mem hwC hx) ((Cen z).inv_mem hwC),
      (Subgroup.mem_normalizer_iff.1 hwN x).1 hxK, ?_⟩
    show toBar z (⟨w, hwC⟩ * ⟨x, hx⟩ * ⟨w, hwC⟩⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => key htC htN hl, fun hl => ?_⟩
  have h1 := key ((Cen z).inv_mem htC) ((normalizer (K : Set G)).inv_mem htN) hl
  have e : toBar z ⟨t⁻¹, (Cen z).inv_mem htC⟩ = (toBar z ⟨t, htC⟩)⁻¹ := by
    show toBar z (⟨t, htC⟩⁻¹) = _
    rw [map_inv]
  rw [e] at h1
  simpa [mul_assoc] using h1

theorem bar_mem_sup_centralizer_of_inner {K : Subgroup G} (hKC : K ≤ Cen z) {t : G}
    (htC : t ∈ Cen z) (hin : ∃ a ∈ K, ∀ k ∈ K, t * k * t⁻¹ = a * k * a⁻¹) :
    toBar z ⟨t, htC⟩ ∈ barOf z K ⊔ centralizer (barOf z K : Set (CentralizerBar z)) := by
  obtain ⟨a, haK, hak⟩ := hin
  have haC : a ∈ Cen z := hKC haK
  have h1 : toBar z ⟨a, haC⟩ ∈ barOf z K := bar_mem_barOf_iff.2 ⟨a, haC, haK, rfl⟩
  have h2 : (toBar z ⟨a, haC⟩)⁻¹ * toBar z ⟨t, htC⟩ ∈
      centralizer (barOf z K : Set (CentralizerBar z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨k, hkC, hkK, rfl⟩ := bar_mem_barOf_iff.1 hl
    have hsub : (⟨t, htC⟩ * ⟨k, hkC⟩ * ⟨t, htC⟩⁻¹ : ↥(Cen z)) =
        ⟨a, haC⟩ * ⟨k, hkC⟩ * ⟨a, haC⟩⁻¹ := Subtype.ext (hak k hkK)
    have hk := congrArg (toBar z) hsub
    simp only [map_mul, map_inv] at hk
    calc toBar z ⟨k, hkC⟩ * ((toBar z ⟨a, haC⟩)⁻¹ * toBar z ⟨t, htC⟩)
        = (toBar z ⟨a, haC⟩)⁻¹ * (toBar z ⟨a, haC⟩ * toBar z ⟨k, hkC⟩ * (toBar z ⟨a, haC⟩)⁻¹) *
            toBar z ⟨t, htC⟩ := by group
      _ = (toBar z ⟨a, haC⟩)⁻¹ * (toBar z ⟨t, htC⟩ * toBar z ⟨k, hkC⟩ * (toBar z ⟨t, htC⟩)⁻¹) *
            toBar z ⟨t, htC⟩ := by rw [hk]
      _ = ((toBar z ⟨a, haC⟩)⁻¹ * toBar z ⟨t, htC⟩) * toBar z ⟨k, hkC⟩ := by group
  have := Subgroup.mul_mem_sup h1 h2
  rwa [mul_inv_cancel_left] at this

end KLevel

theorem inner_mem_LC {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (h : Stage1L4 G z S ε q L₁ L₂) (hSC : S ≤ Cen z)
    {K : Subgroup G} (hKC : K ≤ Cen z) (hKL : barOf z K = L₁ ∨ barOf z K = L₂)
    {t : G} (htS : t ∈ S) (htN : t ∈ normalizer (K : Set G))
    (hin : ∃ a ∈ K, ∀ k ∈ K, t * k * t⁻¹ = a * k * a⁻¹) : t ∈ LC z := by
  have htC : t ∈ Cen z := hSC htS
  have hbar := bar_mem_sup_centralizer_of_inner hKC htC hin
  have hnorm := bar_mem_normalizer_image htC htN
  have hp := h.pair
  rcases hKL with hKL | hKL
  · rw [hKL] at hbar hnorm
    exact inner_mem_LC_bar hSC hp.ne hp.prod hp.comps hp.sl₁ h.pgl.1 hp.swap h.index_le htS htC
      hnorm hbar
  · rw [hKL] at hbar hnorm
    refine inner_mem_LC_bar hSC hp.ne.symm (bar_isCentralProd_symm hp.prod) ?_ hp.sl₂ h.pgl.2 ?_
      h.index_le htS htC hnorm hbar
    · rw [hp.comps]
      exact Set.pair_comm _ _
    · obtain ⟨s, hs, hsC, h1, h2⟩ := hp.swap
      exact ⟨s, hs, hsC, h2, h1⟩

end CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

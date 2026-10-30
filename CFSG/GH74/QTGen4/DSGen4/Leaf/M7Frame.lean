module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.M7Group
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyDict
public import Certificates.Certificate320040

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement Matrix
open Certificates.S3x3GL42 (aI bI aII bII CentFacts TypeIFacts TypeIIFacts fixV Rel RelAB RelC
  NonSing)
open Certificates.A5GL42 (Mat4 Vec4)

namespace M7

variable {G : Type} [Group G]

abbrev QFrame (P : Subgroup G) : Type :=
  ElemFrame P (pCoreOf 2 P) (dsFrattini (pCoreOf 2 P))

section Pre

variable {P E K : Subgroup G}

theorem fixV_zero (a : Mat4) : (0 : Vec4) ∈ fixV a := by
  simp [Certificates.S3x3GL42.fixV]

theorem fixV_add (a : Mat4) : ∀ u ∈ fixV a, ∀ w ∈ fixV a, u + w ∈ fixV a := by
  intro u hu w hw
  simp only [Certificates.S3x3GL42.fixV, Finset.mem_filter, Finset.mem_univ, true_and] at hu hw ⊢
  rw [Matrix.mulVec_add, hu, hw]

theorem K_le_pre (F : ElemFrame P E K) (hKE : K ≤ E) {S : Finset Vec4} (h0 : 0 ∈ S)
    (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S) : K ≤ pre F S h0 hS := by
  intro g hg
  have hgE : g ∈ E := hKE hg
  have h1 : F.φ ⟨g, hgE⟩ = 1 := (F.ker ⟨g, hgE⟩).mpr hg
  refine mem_pre.mpr ⟨⟨g, hgE⟩, rfl, ?_⟩
  rw [h1, toAdd_one]
  exact h0

theorem relIndex_pre (F : ElemFrame P E K) (hKE : K ≤ E) {S : Finset Vec4} (h0 : 0 ∈ S)
    (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S) : K.relIndex (pre F S h0 hS) = S.card := by
  rw [relIndex_eq_card_img F (K_le_pre F hKE h0 hS) (pre_le F h0 hS), img_pre F h0 hS]

theorem pre_inf_pre (F : ElemFrame P E K) (hKE : K ≤ E) {S S' : Finset Vec4} (h0 : 0 ∈ S)
    (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S) (h0' : 0 ∈ S') (hS' : ∀ u ∈ S', ∀ w ∈ S', u + w ∈ S')
    (hSS' : ∀ v ∈ S, v ∈ S' → v = 0) : pre F S h0 hS ⊓ pre F S' h0' hS' = K := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨e, he, hv⟩ := mem_pre.mp hx1
    obtain ⟨e', he', hv'⟩ := mem_pre.mp hx2
    have hee : e' = e := Subtype.ext (he'.trans he.symm)
    rw [hee] at hv'
    have h0v : Multiplicative.toAdd (F.φ e) = 0 := hSS' _ hv hv'
    have hone : F.φ e = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h0v, toAdd_one]
    rw [← he]
    exact (F.ker e).mp hone
  · exact le_inf (K_le_pre F hKE h0 hS) (K_le_pre F hKE h0' hS')

theorem pre_sup_pre (F : ElemFrame P E K) (hKE : K ≤ E) {S S' : Finset Vec4} (h0 : 0 ∈ S)
    (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S) (h0' : 0 ∈ S') (hS' : ∀ u ∈ S', ∀ w ∈ S', u + w ∈ S')
    (hspan : ∀ u : Vec4, ∃ x ∈ S, ∃ y ∈ S', u = x + y) : pre F S h0 hS ⊔ pre F S' h0' hS' = E := by
  apply le_antisymm
  · exact sup_le (pre_le F h0 hS) (pre_le F h0' hS')
  · intro g hg
    have key : ∀ e : ↥E, (e : G) ∈ pre F S h0 hS ⊔ pre F S' h0' hS' := by
      intro e
      obtain ⟨x, hx, y, hy, hxy⟩ := hspan (Multiplicative.toAdd (F.φ e))
      obtain ⟨e₁, he₁⟩ := F.surj (Multiplicative.ofAdd x)
      obtain ⟨e₂, he₂⟩ := F.surj (Multiplicative.ofAdd y)
      have hm1 : (e₁ : G) ∈ pre F S h0 hS :=
        mem_pre.mpr ⟨e₁, rfl, by rw [he₁, toAdd_ofAdd]; exact hx⟩
      have hm2 : (e₂ : G) ∈ pre F S' h0' hS' :=
        mem_pre.mpr ⟨e₂, rfl, by rw [he₂, toAdd_ofAdd]; exact hy⟩
      have hφ : F.φ (e₁ * e₂) = F.φ e := by
        apply Multiplicative.toAdd.injective
        rw [map_mul, toAdd_mul, he₁, he₂, toAdd_ofAdd, toAdd_ofAdd, hxy]
      have hφk : F.φ ((e₁ * e₂)⁻¹ * e) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hφ, toAdd_one]
        exact neg_add_cancel _
      have hkK : (((e₁ * e₂)⁻¹ * e : ↥E) : G) ∈ K := (F.ker _).mp hφk
      have hprod : (e₁ : G) * (e₂ : G) * (((e₁ * e₂)⁻¹ * e : ↥E) : G) = (e : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      have h1 : (e₁ : G) ∈ pre F S h0 hS ⊔ pre F S' h0' hS' := Subgroup.mem_sup_left hm1
      have h2 : (e₂ : G) ∈ pre F S h0 hS ⊔ pre F S' h0' hS' := Subgroup.mem_sup_right hm2
      have h3 : (((e₁ * e₂)⁻¹ * e : ↥E) : G) ∈ pre F S h0 hS ⊔ pre F S' h0' hS' :=
        Subgroup.mem_sup_left (K_le_pre F hKE h0 hS hkK)
      rw [← hprod]
      exact mul_mem (mul_mem h1 h2) h3
    exact key ⟨g, hg⟩

theorem normalizer_pre (F : ElemFrame P E K) (hPE : P ≤ Subgroup.normalizer (E : Set G))
    {S : Finset Vec4} (h0 : 0 ∈ S) (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S)
    (hinv : ∀ p : ↥P, ∀ v ∈ S, glMat (F.M p) *ᵥ v ∈ S) :
    P ≤ Subgroup.normalizer ((pre F S h0 hS : Subgroup G) : Set G) := by
  apply DSBS3.mem_normalizer_of_conj
  intro g hg x hx
  obtain ⟨e, rfl, hv⟩ := mem_pre.mp hx
  refine mem_pre.mpr ⟨conjE hPE ⟨g, hg⟩ e, coe_conjE hPE ⟨g, hg⟩ e, ?_⟩
  have h := F.act ⟨g, hg⟩ e (conjE hPE ⟨g, hg⟩ e) (coe_conjE hPE ⟨g, hg⟩ e)
  rw [← h]
  exact hinv ⟨g, hg⟩ _ hv

theorem fixFree_pre (F : ElemFrame P E K) (hPE : P ≤ Subgroup.normalizer (E : Set G))
    {S : Finset Vec4} (h0 : 0 ∈ S) (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S) (x : ↥P) :
    FixFree K (pre F S h0 hS) (x : G) ↔ ∀ v ∈ S, glMat (F.M x) *ᵥ v = v → v = 0 := by
  unfold FixFree
  constructor
  · intro hff v hv hfix
    obtain ⟨e, he⟩ := F.surj (Multiplicative.ofAdd v)
    have hvec : Multiplicative.toAdd (F.φ e) = v := by rw [he, toAdd_ofAdd]
    have hfixv : glMat (F.M x) *ᵥ Multiplicative.toAdd (F.φ e) =
        Multiplicative.toAdd (F.φ e) := by
      rw [hvec]
      exact hfix
    have hmem : (e : G) ∈ pre F S h0 hS :=
      mem_pre.mpr ⟨e, rfl, by rw [hvec]; exact hv⟩
    have hcomm : ⁅(e : G), (x : G)⁆ ∈ K :=
      (comm_mem_K_iff (F := F) hPE x.2 e.2).mpr hfixv
    have h1 : F.φ e = 1 := (F.ker e).mpr (hff _ hmem hcomm)
    rw [← hvec, h1, toAdd_one]
  · intro hfix e he hcomm
    obtain ⟨e', rfl, hv⟩ := mem_pre.mp he
    have hfixv : glMat (F.M x) *ᵥ Multiplicative.toAdd (F.φ e') =
        Multiplicative.toAdd (F.φ e') :=
      (comm_mem_K_iff (F := F) hPE x.2 e'.2).mp hcomm
    have h0v : Multiplicative.toAdd (F.φ e') = 0 := hfix _ hv hfixv
    have h1 : F.φ e' = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h0v, toAdd_one]
    exact (F.ker e').mp h1

theorem comm_pre_iff (F : ElemFrame P E K) (hPE : P ≤ Subgroup.normalizer (E : Set G))
    {S : Finset Vec4} (h0 : 0 ∈ S) (hS : ∀ u ∈ S, ∀ w ∈ S, u + w ∈ S) (x : ↥P) :
    (∀ w ∈ pre F S h0 hS, ⁅(x : G), w⁆ ∈ K) ↔ ∀ v ∈ S, glMat (F.M x) *ᵥ v = v := by
  constructor
  · intro h v hv
    obtain ⟨e, he⟩ := F.surj (Multiplicative.ofAdd v)
    have hvec : Multiplicative.toAdd (F.φ e) = v := by rw [he, toAdd_ofAdd]
    have hmem : (e : G) ∈ pre F S h0 hS :=
      mem_pre.mpr ⟨e, rfl, by rw [hvec]; exact hv⟩
    have hfixv : glMat (F.M x) *ᵥ Multiplicative.toAdd (F.φ e) =
        Multiplicative.toAdd (F.φ e) :=
      (comm_mem_K_iff' (F := F) hPE x.2 e.2).mp (h _ hmem)
    rw [hvec] at hfixv
    exact hfixv
  · intro hall w hw
    obtain ⟨e, rfl, hv⟩ := mem_pre.mp hw
    exact (comm_mem_K_iff' (F := F) hPE x.2 e.2).mpr (hall _ hv)

theorem img_inv_of_normalizer (F : ElemFrame P E K) (hPE : P ≤ Subgroup.normalizer (E : Set G))
    {X : Subgroup G} (hX : P ≤ Subgroup.normalizer (X : Set G)) (p : ↥P) {v : Vec4}
    (hv : v ∈ img F X) : glMat (F.M p) *ᵥ v ∈ img F X := by
  obtain ⟨e, heX, rfl⟩ := mem_img.mp hv
  have hconj : ((conjE hPE p e : ↥E) : G) ∈ X := by
    rw [coe_conjE hPE p e]
    exact (Subgroup.mem_normalizer_iff.mp (hX p.2) (e : G)).mp heX
  exact mem_img.mpr ⟨conjE hPE p e, hconj,
    (F.act p e (conjE hPE p e) (coe_conjE hPE p e)).symm⟩

end Pre

variable [Finite G] {L P : Subgroup G} {d k t : G}

theorem Ctx.frame_ker [DSLeaf LeafFrattiniFaithful] (h : Ctx L P d k t) (F : QFrame P) :
    ∀ p : ↥P, F.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P := by
  have hQ : IsPGroup 2 (pCoreOf 2 P) :=
    CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 P
  have hPQ : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P
  intro p
  constructor
  · intro hp1
    exact frattini_faithful h.hchar (p : G) p.2
      (fun q hq => ElemFrame.comm_mem_of_M_eq_one F hPQ p hp1 hq)
  · intro hp
    exact ElemFrame.M_eq_one F hPQ p
      (fun e he => frattiniChief_comm_mem (pCoreOf 2 P) hQ hp he)

theorem glMat_cube_eq_one (x : GL (Fin 4) (ZMod 2)) (hx : x ^ 3 = 1) :
    glMat x * glMat x * glMat x = 1 := by
  have h := congrArg Units.val hx
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_three'] at h
  exact h

theorem glMat_sq_eq_one (x : GL (Fin 4) (ZMod 2)) (hx : x ^ 2 = 1) :
    glMat x * glMat x = 1 := by
  have h := congrArg Units.val hx
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two] at h
  exact h

theorem glMat_ne_one (x : GL (Fin 4) (ZMod 2)) (hx : x ≠ 1) : glMat x ≠ 1 :=
  fun h1 => hx (Units.ext h1)

theorem glMat_comm_of_comm (x y : GL (Fin 4) (ZMod 2)) (hxy : x * y = y * x) :
    glMat x * glMat y = glMat y * glMat x := by
  have h := congrArg Units.val hxy
  rw [Units.val_mul, Units.val_mul] at h
  exact h

theorem glMat_inverts (c a : GL (Fin 4) (ZMod 2)) (h : c * a = a ^ 2 * c) :
    glMat c * glMat a = glMat a * glMat a * glMat c := by
  have h' := congrArg Units.val h
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, pow_two] at h'
  exact h'

theorem Ctx.rel_mat (h : Ctx L P d k t) (F : QFrame P)
    (hker : ∀ p : ↥P, F.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P) :
    Rel (glMat (F.M h.kP)) (glMat (F.M h.dP)) (glMat (F.M h.tP)) := by
  obtain ⟨ha3, ha1, hb3, hb1, hc2, hca, hba, hbc, -, -⟩ := h.rel F.M hker
  unfold Certificates.S3x3GL42.Rel Certificates.S3x3GL42.RelAB Certificates.S3x3GL42.RelC
  exact ⟨⟨glMat_cube_eq_one _ ha3, glMat_ne_one _ ha1, glMat_cube_eq_one _ hb3, glMat_ne_one _ hb1, glMat_comm_of_comm _ _ hba.symm⟩,
    glMat_sq_eq_one _ hc2, glMat_inverts _ _ hca, glMat_comm_of_comm _ _ hbc⟩

theorem conj_eq_one_iff (g x : GL (Fin 4) (ZMod 2)) : g * x * g⁻¹ = 1 ↔ x = 1 := by
  simp

theorem Ctx.exists_std_frame (h : Ctx L P d k t) (F₀ : QFrame P)
    (hker₀ : ∀ p : ↥P, F₀.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P) :
    ∃ F : QFrame P, (∀ p : ↥P, F.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P) ∧
      ((glMat (F.M h.kP) = aI ∧ glMat (F.M h.dP) = bI) ∨
        (glMat (F.M h.kP) = aII ∧ glMat (F.M h.dP) = bII)) := by
  obtain ⟨g, hg, hcase⟩ :=
    (Certificates.certificate320040).classify _ _ _ (h.rel_mat F₀ hker₀)
  let gGL : GL (Fin 4) (ZMod 2) :=
    Matrix.GeneralLinearGroup.mk'' g (by rw [hg]; exact isUnit_one)
  have hgl : glMat gGL = g := rfl
  have hkerF : ∀ p : ↥P, (F₀.conj gGL).M p = 1 ↔ (p : G) ∈ pCoreOf 2 P := by
    intro p
    rw [ElemFrame.conj_M]
    exact (conj_eq_one_iff _ _).trans (hker₀ p)
  refine ⟨F₀.conj gGL, hkerF, ?_⟩
  rcases hcase with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
  · left
    constructor
    · rw [ElemFrame.conj_M]
      exact glMat_conj_eq (g := gGL) (u := F₀.M h.kP) (m := aI) (by rw [hgl]; exact hga)
    · rw [ElemFrame.conj_M]
      exact glMat_conj_eq (g := gGL) (u := F₀.M h.dP) (m := bI) (by rw [hgl]; exact hgb)
  · right
    constructor
    · rw [ElemFrame.conj_M]
      exact glMat_conj_eq (g := gGL) (u := F₀.M h.kP) (m := aII) (by rw [hgl]; exact hga)
    · rw [ElemFrame.conj_M]
      exact glMat_conj_eq (g := gGL) (u := F₀.M h.dP) (m := bII) (by rw [hgl]; exact hgb)

theorem Ctx.relIndex_dvd_six (h : Ctx L P d k t) (F : QFrame P)
    (hker : ∀ p : ↥P, F.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P)
    (hcent : CentFacts (glMat (F.M h.kP)) (glMat (F.M h.dP)) (glMat (F.M h.tP))) :
    (pCoreOf 2 P).relIndex (dsCentMod P L (pCoreOf 2 P)) ∣ 6 := by
  obtain ⟨T, hTlen, hTall, -⟩ := hcent
  have hCP : dsCentMod P L (pCoreOf 2 P) ≤ P := fun x hx => hx.1
  let f : ↥(dsCentMod P L (pCoreOf 2 P)) →* GL (Fin 4) (ZMod 2) :=
    F.M.comp (Subgroup.inclusion hCP)
  have hf : ∀ c : ↥(dsCentMod P L (pCoreOf 2 P)), f c = F.M ⟨(c : G), hCP c.2⟩ :=
    fun c => rfl
  have hker_f : f.ker = (pCoreOf 2 P).subgroupOf (dsCentMod P L (pCoreOf 2 P)) := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf]
    exact hker ⟨(c : G), hCP c.2⟩
  have hrel : (pCoreOf 2 P).relIndex (dsCentMod P L (pCoreOf 2 P)) = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker_f, Subgroup.index_ker]
  have hTmem : ∀ g ∈ f.range, glMat g ∈ T := by
    intro g hg
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hg
    have hk : glMat (f c) * glMat (F.M h.kP) = glMat (F.M h.kP) * glMat (f c) := by
      have e := congrArg Units.val
        (Ctx.cent_comm h F.M hker ⟨(c : G), hCP c.2⟩ c.2 k h.hk)
      rw [Units.val_mul, Units.val_mul] at e
      rw [hf]
      exact e
    have ht : glMat (f c) * glMat (F.M h.tP) = glMat (F.M h.tP) * glMat (f c) := by
      have e := congrArg Units.val
        (Ctx.cent_comm h F.M hker ⟨(c : G), hCP c.2⟩ c.2 t h.ht)
      rw [Units.val_mul, Units.val_mul] at e
      rw [hf]
      exact e
    have hns : Certificates.S3x3GL42.NonSing (glMat (f c)) := by
      intro v hv
      calc v = glMat ((f c)⁻¹) *ᵥ (glMat (f c) *ᵥ v) := by
            rw [Matrix.mulVec_mulVec, ElemFrame.glMat_inv_mul, Matrix.one_mulVec]
        _ = 0 := by rw [hv, Matrix.mulVec_zero]
    exact hTall _ hk ht hns
  have hcard_le : Nat.card f.range ≤ 6 := by
    classical
    have hmem : ∀ g : ↥f.range, glMat (g : GL (Fin 4) (ZMod 2)) ∈ T.toFinset :=
      fun g => List.mem_toFinset.mpr (hTmem _ g.2)
    let ι : ↥f.range → ↥T.toFinset := fun g => ⟨glMat (g : GL (Fin 4) (ZMod 2)), hmem g⟩
    have hι : Function.Injective ι := by
      intro g₁ g₂ heq
      exact Subtype.ext (Units.ext (congrArg Subtype.val heq))
    have h1 : Nat.card ↥f.range ≤ Nat.card ↥T.toFinset := Nat.card_le_card_of_injective ι hι
    have h2 : Nat.card ↥T.toFinset = T.toFinset.card := Nat.card_eq_finsetCard T.toFinset
    have h3 : T.toFinset.card ≤ T.length := List.toFinset_card_le (l := T)
    omega
  haveI : Finite ↥f.range :=
    Finite.of_surjective f.rangeRestrict (MonoidHom.rangeRestrict_surjective f)
  have hdmem : F.M h.dP ∈ f.range :=
    MonoidHom.mem_range.mpr ⟨⟨d, h.d_mem_cent⟩, rfl⟩
  have hdord : orderOf (⟨F.M h.dP, hdmem⟩ : ↥f.range) = 3 := by
    rw [Subgroup.orderOf_mk]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨-, -, hd3, hd1, -⟩ := h.rel F.M hker
    exact orderOf_eq_prime hd3 hd1
  have h3 : 3 ∣ Nat.card f.range := by
    have := orderOf_dvd_natCard (⟨F.M h.dP, hdmem⟩ : ↥f.range)
    rwa [hdord] at this
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  rw [hrel]
  have h36 : Nat.card f.range = 3 ∨ Nat.card f.range = 6 := by omega
  rcases h36 with h36 | h36 <;> rw [h36] <;> norm_num

theorem pow_mulVec_fix {a : Mat4} {v : Vec4} (hv : a *ᵥ v = v) (n : ℕ) :
    a ^ n *ᵥ v = v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hv]
    exact ih

theorem Ctx.inv_fixV_a (h : Ctx L P d k t) (F : QFrame P)
    (hker : ∀ p : ↥P, F.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P) (p : ↥P) (v : Vec4)
    (hv : v ∈ fixV (glMat (F.M h.kP))) :
    glMat (F.M p) *ᵥ v ∈ fixV (glMat (F.M h.kP)) := by
  simp only [Certificates.S3x3GL42.fixV, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, h10⟩ := h.rel F.M hker
  have hx1L : (p : G)⁻¹ * k * (p : G) ∈ L := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (h.hPL (P.inv_mem p.2)) k).mp h.hk
    rw [inv_inv] at h1
    exact h1
  have hx1o : orderOf ((p : G)⁻¹ * k * (p : G)) = 3 := by
    have h1 := orderOf_injective (MulAut.conj (p : G)⁻¹).toMonoidHom
      (MulAut.conj (p : G)⁻¹).injective k
    have h2 : (MulAut.conj (p : G)⁻¹).toMonoidHom k = (p : G)⁻¹ * k * (p : G) := by
      simp [MulAut.conj_apply]
    rw [h2, h.hk3] at h1
    exact h1
  have hsub : (⟨(p : G)⁻¹ * k * (p : G), h.hLP hx1L⟩ : ↥P) = p⁻¹ * h.kP * p :=
    Subtype.ext rfl
  have hGL : F.M p * F.M ⟨(p : G)⁻¹ * k * (p : G), h.hLP hx1L⟩ = F.M h.kP * F.M p := by
    rw [hsub, map_mul, map_mul, map_inv]
    group
  have hmat : glMat (F.M p) * glMat (F.M ⟨(p : G)⁻¹ * k * (p : G), h.hLP hx1L⟩) =
      glMat (F.M h.kP) * glMat (F.M p) := by
    have := congrArg Units.val hGL
    simpa only [Units.val_mul] using this
  have hpow2 : glMat (F.M h.kP ^ 2) = glMat (F.M h.kP) ^ 2 := Units.val_pow_eq_pow_val _ _
  have hX : glMat (F.M ⟨(p : G)⁻¹ * k * (p : G), h.hLP hx1L⟩) *ᵥ v = v := by
    rcases h10 _ hx1L hx1o with h1 | h1
    · rw [h1]
      exact hv
    · rw [h1, hpow2]
      exact pow_mulVec_fix hv 2
  rw [Matrix.mulVec_mulVec, ← hmat, ← Matrix.mulVec_mulVec, hX]

theorem Ctx.inv_fixV_b (h : Ctx L P d k t) (F : QFrame P)
    (hker : ∀ p : ↥P, F.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P)
    (hcent : CentFacts (glMat (F.M h.kP)) (glMat (F.M h.dP)) (glMat (F.M h.tP))) (p : ↥P)
    (v : Vec4) (hv : v ∈ fixV (glMat (F.M h.dP))) :
    glMat (F.M p) *ᵥ v ∈ fixV (glMat (F.M h.dP)) := by
  obtain ⟨x, hxP⟩ : ∃ x : ↥P, x = p⁻¹ * h.dP * p := ⟨_, rfl⟩
  have hx : (x : G) = (p : G)⁻¹ * d * p := congrArg Subtype.val hxP
  have hxC : (x : G) ∈ dsCentMod P L (pCoreOf 2 P) := by
    show (x : G) ∈ P ∧ (x : G) ∈ Subgroup.normalizer (pCoreOf 2 P : Set G) ∧
      ∀ l ∈ L, ⁅(x : G), l⁆ ∈ pCoreOf 2 P
    refine ⟨x.2, CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P x.2, ?_⟩
    intro l hl
    have hl' : (p : G) * l * (p : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (h.hPL p.2) l).mp hl
    have hc : ⁅d, (p : G) * l * (p : G)⁻¹⁆ ∈ pCoreOf 2 P := h.hdc _ hl'
    have hN : (p : G)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
      Subgroup.inv_mem _ (CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P p.2)
    have key : ⁅(x : G), l⁆ = (p : G)⁻¹ * ⁅d, (p : G) * l * (p : G)⁻¹⁆ * ((p : G)⁻¹)⁻¹ := by
      rw [hx]
      simp only [commutatorElement_def]
      group
    rw [key]
    exact (Subgroup.mem_normalizer_iff.mp hN _).mp hc
  have hcK : F.M x * F.M h.kP = F.M h.kP * F.M x := h.cent_comm F.M hker x hxC k h.hk
  have hcT : F.M x * F.M h.tP = F.M h.tP * F.M x := h.cent_comm F.M hker x hxC t h.ht
  have hcKM : glMat (F.M x) * glMat (F.M h.kP) = glMat (F.M h.kP) * glMat (F.M x) := by
    have := congrArg Units.val hcK
    simpa only [Units.val_mul] using this
  have hcTM : glMat (F.M x) * glMat (F.M h.tP) = glMat (F.M h.tP) * glMat (F.M x) := by
    have := congrArg Units.val hcT
    simpa only [Units.val_mul] using this
  have hNS : Certificates.S3x3GL42.NonSing (glMat (F.M x)) := by
    intro w hw
    calc w = (glMat (F.M x)⁻¹ * glMat (F.M x)) *ᵥ w := by
          rw [ElemFrame.glMat_inv_mul, Matrix.one_mulVec]
      _ = glMat (F.M x)⁻¹ *ᵥ (glMat (F.M x) *ᵥ w) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hw, Matrix.mulVec_zero]
  have hd3 : d ^ 3 = 1 := by
    have := pow_orderOf_eq_one d
    rwa [h.hd3] at this
  have hx3G : (x : G) ^ 3 = 1 := by
    have e : ((p : G)⁻¹ * d * (p : G)) ^ 3 = (p : G)⁻¹ * d ^ 3 * (p : G) := by
      simp only [pow_three']
      group
    rw [hx, e, hd3]
    simp
  have hx3P : x ^ 3 = 1 := Subtype.ext (by simpa using hx3G)
  have hcube : glMat (F.M x) * glMat (F.M x) * glMat (F.M x) = 1 := by
    have h3 : F.M x ^ 3 = 1 := by rw [← map_pow, hx3P, map_one]
    have h4 := congrArg Units.val h3
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_three'] at h4
    exact h4
  obtain ⟨T, -, hTall, hTcube⟩ := hcent
  have hmemT : glMat (F.M x) ∈ T := hTall _ hcKM hcTM hNS
  have hbv : glMat (F.M h.dP) *ᵥ v = v := by
    simpa only [Certificates.S3x3GL42.fixV, Finset.mem_filter, Finset.mem_univ, true_and] using hv
  have hfix : glMat (F.M x) *ᵥ v = v := by
    rcases hTcube _ hmemT hcube with h1 | h1 | h1
    · rw [h1, Matrix.one_mulVec]
    · rw [h1, hbv]
    · rw [h1, ← Matrix.mulVec_mulVec, hbv, hbv]
  have hconj : F.M h.dP * F.M p = F.M p * F.M x := by
    rw [hxP, map_mul, map_mul, map_inv]
    group
  have hconjM : glMat (F.M h.dP) * glMat (F.M p) = glMat (F.M p) * glMat (F.M x) := by
    have := congrArg Units.val hconj
    simpa only [Units.val_mul] using this
  simp only [Certificates.S3x3GL42.fixV, Finset.mem_filter, Finset.mem_univ, true_and]
  calc glMat (F.M h.dP) *ᵥ (glMat (F.M p) *ᵥ v)
      = (glMat (F.M h.dP) * glMat (F.M p)) *ᵥ v := by rw [Matrix.mulVec_mulVec]
    _ = (glMat (F.M p) * glMat (F.M x)) *ᵥ v := by rw [hconjM]
    _ = glMat (F.M p) *ᵥ (glMat (F.M x) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = glMat (F.M p) *ᵥ v := by rw [hfix]

theorem Ctx.fix_of_L (h : Ctx L P d k t) (F : QFrame P)
    (hker : ∀ p : ↥P, F.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P) (l : G) (hl : l ∈ L) (v : Vec4)
    (hva : glMat (F.M h.kP) *ᵥ v = v) (hvc : glMat (F.M h.tP) *ᵥ v = v) :
    glMat (F.M ⟨l, h.hLP hl⟩) *ᵥ v = v := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := h.rel F.M hker
  obtain ⟨i, j, hij⟩ := h9 l hl
  have hu : glMat (F.M ⟨l, h.hLP hl⟩) = glMat (F.M h.tP) ^ i * glMat (F.M h.kP) ^ j := by
    rw [hij]
    simp only [glMat, Units.val_mul, Units.val_pow_eq_pow_val]
  rw [hu, ← Matrix.mulVec_mulVec, pow_mulVec_fix hva j, pow_mulVec_fix hvc i]

theorem Ctx.type1_of_frame (h : Ctx L P d k t) (F : QFrame P)
    (hker : ∀ p : ↥P, F.M p = 1 ↔ (p : G) ∈ pCoreOf 2 P)
    (hA : glMat (F.M h.kP) = aI) (hB : glMat (F.M h.dP) = bI)
    (hcent : CentFacts aI bI (glMat (F.M h.tP))) (hI : TypeIFacts aI bI (glMat (F.M h.tP))) :
    S3Type1 P L k d := by
  have hPQ : P ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P
  have hΦQ : dsFrattini (pCoreOf 2 P) ≤ pCoreOf 2 P := Subgroup.map_subtype_le _
  obtain ⟨hcard_a, hcard_b, hinter, hc_fix, hspan⟩ := hI
  have h0a : (0 : Vec4) ∈ fixV aI := fixV_zero aI
  have hSa := fixV_add aI
  have h0b : (0 : Vec4) ∈ fixV bI := fixV_zero bI
  have hSb := fixV_add bI
  have hinva : ∀ p : ↥P, ∀ v ∈ fixV aI, glMat (F.M p) *ᵥ v ∈ fixV aI := by
    intro p v hv
    have := h.inv_fixV_a F hker p v (by rw [hA]; exact hv)
    rwa [hA] at this
  have hinvb : ∀ p : ↥P, ∀ v ∈ fixV bI, glMat (F.M p) *ᵥ v ∈ fixV bI := by
    intro p v hv
    have := h.inv_fixV_b F hker (by rw [hA, hB]; exact hcent) p v (by rw [hB]; exact hv)
    rwa [hB] at this
  have hfixa : ∀ v, v ∈ fixV aI ↔ aI *ᵥ v = v := by
    intro v; simp [Certificates.S3x3GL42.fixV]
  have hfixb : ∀ v, v ∈ fixV bI ↔ bI *ᵥ v = v := by
    intro v; simp [Certificates.S3x3GL42.fixV]
  refine ⟨pre F (fixV aI) h0a hSa, pre F (fixV bI) h0b hSb, K_le_pre F hΦQ h0a hSa,
    pre_le F h0a hSa, K_le_pre F hΦQ h0b hSb, pre_le F h0b hSb,
    normalizer_pre F hPQ h0a hSa hinva, normalizer_pre F hPQ h0b hSb hinvb,
    pre_inf_pre F hΦQ h0a hSa h0b hSb hinter, pre_sup_pre F hΦQ h0a hSa h0b hSb hspan,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [relIndex_pre F hΦQ h0a hSa]; exact hcard_a
  · rw [relIndex_pre F hΦQ h0b hSb]; exact hcard_b
  · intro l hl
    refine (comm_pre_iff F hPQ h0a hSa ⟨l, h.hLP hl⟩).mpr (fun v hv => ?_)
    refine h.fix_of_L F hker l hl v ?_ (hc_fix v hv)
    rw [hA]; exact (hfixa v).mp hv
  · refine (fixFree_pre F hPQ h0a hSa h.dP).mpr (fun v hv hbv => hinter v hv ?_)
    rw [hB] at hbv
    exact (hfixb v).mpr hbv
  · refine (comm_pre_iff F hPQ h0b hSb h.dP).mpr (fun v hv => ?_)
    rw [hB]; exact (hfixb v).mp hv
  · refine (fixFree_pre F hPQ h0b hSb h.kP).mpr (fun v hv hav => hinter v ?_ hv)
    rw [hA] at hav
    exact (hfixa v).mpr hav
  · by_contra hcon
    push Not at hcon
    have hk' := hcon k h.hk
    have h2 := (comm_pre_iff F hPQ h0b hSb h.kP).mp hk'
    obtain ⟨v, hv, hv0⟩ := Finset.exists_mem_ne (by omega : 1 < (fixV bI).card) 0
    apply hv0
    refine hinter v ?_ hv
    have := h2 v hv
    rw [hA] at this
    exact (hfixa v).mpr this

theorem Ctx.type2_of_frame (h : Ctx L P d k t) (F : QFrame P)
    (hA : glMat (F.M h.kP) = aII) (hB : glMat (F.M h.dP) = bII)
    (hII : TypeIIFacts aII bII (glMat (F.M h.tP))) :
    S3Type2 P k d := by
  obtain ⟨hfa, hfb, hirr⟩ := hII
  have hPQ : P ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P
  have hΦQ : dsFrattini (pCoreOf 2 P) ≤ pCoreOf 2 P := Subgroup.map_subtype_le _
  unfold S3Type2
  refine ⟨?_, ?_, ?_⟩
  · exact (fixFree_iff F hPQ h.kP).mpr (fun v hv => hfa v (by rw [← hA]; exact hv))
  · exact (fixFree_iff F hPQ h.dP).mpr (fun v hv => hfb v (by rw [← hB]; exact hv))
  · intro X hΦX hXQ hXN
    have hinv : ∀ v ∈ img F X, aII *ᵥ v ∈ img F X ∧ bII *ᵥ v ∈ img F X ∧
        glMat (F.M h.tP) *ᵥ v ∈ img F X := by
      intro v hv
      refine ⟨?_, ?_, ?_⟩
      · rw [← hA]; exact img_inv_of_normalizer F hPQ hXN h.kP hv
      · rw [← hB]; exact img_inv_of_normalizer F hPQ hXN h.dP hv
      · exact img_inv_of_normalizer F hPQ hXN h.tP hv
    by_cases hall : ∀ v ∈ img F X, v = 0
    · left
      have hS : img F X = {0} := by
        ext v
        rw [Finset.mem_singleton]
        refine ⟨hall v, fun hv => ?_⟩
        rw [hv]
        exact zero_mem_img F X
      exact ext_of_img F hΦX hXQ le_rfl hΦQ (by rw [hS, img_bot_of_ker])
    · right
      push Not at hall
      obtain ⟨v, hv, hv0⟩ := hall
      have hgen := hirr (img F X) (zero_mem_img F X)
        (fun u hu w hw => add_mem_img F X hu hw) hinv ⟨v, hv, hv0⟩
      exact ext_of_img F hΦX hXQ hΦQ le_rfl (by rw [img_top F]; exact hgen)

end M7

end CFSG.GH74.QTGen4.DSGen4

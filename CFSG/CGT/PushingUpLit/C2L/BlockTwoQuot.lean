module

public import CFSG.Timmesfeld.RankOne.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.CGT.PushingUpLit.C2L.BlockTwo
import CFSG.Timmesfeld.Bridge.RootSetsSyl

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG.ABGLocalTools
open scoped commutatorElement

private theorem card_eq_card_map_mul_card_inf_ker {R S : Type*} [Group R] [Group S]
    (φ : R →* S) (H : Subgroup R) :
    Nat.card H = Nat.card (H.map φ) * Nat.card (H ⊓ φ.ker : Subgroup R) := by
  let ψ : H →* S := φ.comp H.subtype
  have hrange : ψ.range = H.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ψ.ker = Nat.card (H ⊓ φ.ker : Subgroup R) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : H) : R), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker]

private theorem isSylowOf_map_conj_of_mem {G : Type} [Group G] [Finite G] {T N : Subgroup G}
    (hT : IsSylowOf 2 T N) {g : G} (hg : g ∈ N) :
    IsSylowOf 2 (T.map (MulAut.conj g).toMonoidHom) N := by
  have hNg : N.map (MulAut.conj g).toMonoidHom = N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hg)
  rw [isSylowOf_iff] at hT ⊢
  obtain ⟨hle, hp, hdvd⟩ := hT
  have hidx := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) T N
    (MulAut.conj g).injective
  rw [hNg] at hidx
  exact ⟨(Subgroup.map_mono hle).trans hNg.le, hp.map _, hidx ▸ hdvd⟩

theorem exists_block_of_isTI_quotient {G : Type} [Group G]
    [Finite G] {N D T : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hDT : D ≤ T) (hTN : T ≤ N) (hDN : N ≤ Subgroup.normalizer (D : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T N)
    (hTD : ∀ x ∈ T, ∀ y ∈ T, x * x ∈ D ∧ ⁅x, y⁆ ∈ D)
    (hcard : Nat.card T = 2 ^ n * Nat.card D)
    (hTI : ∀ S₁ S₂ : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S₁ N →
      CFSG.ABGLocalTools.IsSylowOf 2 S₂ N → S₁ ≠ S₂ → S₁ ⊓ S₂ ≤ D)
    (hne : ¬ N ≤ Subgroup.normalizer (T : Set G)) :
    ∃ L : Subgroup G, D ≤ L ∧ T ≤ L ∧ L ≤ N ∧
      (∀ g ∈ N, ∀ x ∈ L, g * x * g⁻¹ ∈ L) ∧
      (∃ φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        Function.Surjective φ ∧ φ.ker = D.subgroupOf L ∧
        (T.subgroupOf L).map φ = CFSG.Timmesfeld.upperUnipotent (GaloisField 2 n)) ∧
      ∀ a ∈ N, a ∉ Subgroup.normalizer (T : Set G) →
        L = T ⊔ T.map (MulAut.conj a).toMonoidHom := by
  classical
  have hDN' : D ≤ N := hDT.trans hTN
  have : (D.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDN').2 hDN
  obtain ⟨π, hπsurj, hker⟩ : ∃ π : ↥N →* ↥N ⧸ D.subgroupOf N,
      Function.Surjective π ∧ π.ker = D.subgroupOf N :=
    ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩
  have hπ1 : ∀ x : N, π x = 1 ↔ (x : G) ∈ D := fun x => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hKT : D.subgroupOf N ≤ T.subgroupOf N := fun x hx => hDT hx
  obtain ⟨B, hB⟩ : ∃ B : Subgroup (↥N ⧸ D.subgroupOf N), B = (T.subgroupOf N).map π :=
    ⟨_, rfl⟩
  have hcomapB : B.comap π = T.subgroupOf N := by
    rw [hB, Subgroup.comap_map_eq, hker, sup_eq_left.2 hKT]
  have hconjB : ∀ g : N, B.map (MulAut.conj (π g)).toMonoidHom =
      ((T.subgroupOf N).map (MulAut.conj g).toMonoidHom).map π := by
    intro g
    have hcomp : (MulAut.conj (π g)).toMonoidHom.comp π = π.comp (MulAut.conj g).toMonoidHom :=
      MonoidHom.ext fun x => by simp
    rw [hB, Subgroup.map_map, Subgroup.map_map, hcomp]
  have hKg : ∀ g : N, D.subgroupOf N ≤ (T.subgroupOf N).map (MulAut.conj g).toMonoidHom := by
    intro g x hx
    refine ⟨g⁻¹ * x * g, hDT ?_, by simp [mul_assoc]⟩
    exact (Subgroup.mem_normalizer_iff''.1 (hDN g.2) x).1 hx
  have hiff : ∀ g : N, B.map (MulAut.conj (π g)).toMonoidHom = B ↔
      T.map (MulAut.conj (g : G)).toMonoidHom = T := by
    intro g
    rw [hconjB, ← CFSG.Timmesfeld.Bridge.map_conj_subgroupOf_eq_self_iff hTN g]
    constructor
    · intro h
      have h' := congrArg (Subgroup.comap π) h
      rwa [Subgroup.comap_map_eq, hker, sup_eq_left.2 (hKg g), hcomapB] at h'
    · intro h
      rw [h, hB]
  have hcardB : Nat.card B = 2 ^ n := by
    have h1 := card_eq_card_map_mul_card_inf_ker π (T.subgroupOf N)
    rw [hker, inf_eq_right.2 hKT, ← hB] at h1
    have h2 : Nat.card (T.subgroupOf N) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
    have h3 : Nat.card (D.subgroupOf N) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN').toEquiv
    rw [h2, h3, hcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have hBexp : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    rw [hB] at hb
    obtain ⟨t, ht, rfl⟩ := hb
    rw [← map_mul, hπ1]
    exact (hTD t ht t ht).1
  have hBp : IsPGroup 2 B := by
    rw [hB]
    exact (hT.isPGroup.comap_subtype (K := N)).map π
  have hBi : ¬ 2 ∣ B.index := by
    rw [← Subgroup.index_comap_of_surjective B hπsurj, hcomapB]
    exact (isSylowOf_iff.1 hT).2.2
  have hBTI : CFSG.Open.fusionIsTI B := by
    intro x hx
    obtain ⟨g, rfl⟩ := hπsurj x
    have hgT : T.map (MulAut.conj (g : G)).toMonoidHom ≠ T := fun h => hx ((hiff g).2 h)
    have hinf := hTI _ _ hT (isSylowOf_map_conj_of_mem hT g.2) (Ne.symm hgT)
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hb1, hb2⟩ := Subgroup.mem_inf.1 hb
    rw [hconjB] at hb2
    rw [hB] at hb1
    obtain ⟨t, ht, rfl⟩ := hb1
    obtain ⟨s, hs, hst⟩ := hb2
    have hts : t⁻¹ * s ∈ D.subgroupOf N := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel]
    have hsT : (s : G) ∈ T := by
      have h1 : t * (t⁻¹ * s) ∈ T.subgroupOf N := (T.subgroupOf N).mul_mem ht (hKT hts)
      rw [mul_inv_cancel_left] at h1
      exact h1
    have hsT' : (s : G) ∈ T.map (MulAut.conj (g : G)).toMonoidHom := by
      rw [← CFSG.Timmesfeld.Bridge.map_subtype_map_conj_subgroupOf hTN g]
      exact ⟨s, hs, rfl⟩
    rw [Subgroup.mem_bot, ← hst, hπ1]
    exact hinf (Subgroup.mem_inf.2 ⟨hsT, hsT'⟩)
  have hBne : Subgroup.normalizer (B : Set (↥N ⧸ D.subgroupOf N)) ≠ ⊤ := by
    intro htop
    apply hne
    intro g hg
    have hmem : π ⟨g, hg⟩ ∈ Subgroup.normalizer (B : Set (↥N ⧸ D.subgroupOf N)) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      ((hiff ⟨g, hg⟩).1 (Subgroup.mem_normalizer_iff_map_conj_eq.1 hmem))
  obtain ⟨B', hB'⟩ : ∃ B' : Sylow 2 (↥N ⧸ D.subgroupOf N), (B' : Subgroup _) = B :=
    ⟨hBp.toSylow hBi, IsPGroup.toSylow_coe hBp hBi⟩
  obtain ⟨Y, hYn, hBY, φY, hφY, hgen⟩ := exists_normal_mulEquiv_SL2_of_isTI B' hn
    (by rw [hB']; exact hcardB) (by rw [hB']; exact hBexp) (by rw [hB']; exact hBTI)
    (by rw [hB']; exact hBne)
  rw [hB'] at hBY hφY hgen
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, L = (Y.comap π).map N.subtype := ⟨_, rfl⟩
  have hmemL : ∀ x : N, (x : G) ∈ L ↔ π x ∈ Y := by
    intro x
    rw [hL]
    constructor
    · rintro ⟨y, hy, hyx⟩
      obtain rfl : y = x := Subtype.ext hyx
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hLN : L ≤ N := by
    rw [hL]
    exact Subgroup.map_subtype_le _
  have hDL : D ≤ L := fun d hd => (hmemL ⟨d, hDN' hd⟩).2 (by
    rw [(hπ1 _).2 hd]
    exact Y.one_mem)
  have hTL : T ≤ L := fun t ht => (hmemL ⟨t, hTN ht⟩).2 (hBY (by
    rw [hB]
    exact ⟨⟨t, hTN ht⟩, ht, rfl⟩))
  have hNL : ∀ g ∈ N, ∀ x ∈ L, g * x * g⁻¹ ∈ L := by
    intro g hg x hx
    have hxN := hLN hx
    have hx' := (hmemL ⟨x, hxN⟩).1 hx
    have hgx : g * x * g⁻¹ ∈ N := N.mul_mem (N.mul_mem hg hxN) (N.inv_mem hg)
    refine (hmemL ⟨_, hgx⟩).2 ?_
    have h1 : (⟨g * x * g⁻¹, hgx⟩ : N) = ⟨g, hg⟩ * ⟨x, hxN⟩ * (⟨g, hg⟩ : N)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact hYn.conj_mem _ hx' _
  have hincl : ∀ (x : N) (hx : (x : G) ∈ L), Subgroup.inclusion hLN ⟨x, hx⟩ = x :=
    fun _ _ => rfl
  have hψmem : ∀ l : L, π (Subgroup.inclusion hLN l) ∈ Y := fun l =>
    (hmemL (Subgroup.inclusion hLN l)).1 l.2
  obtain ⟨ψ, hψ⟩ : ∃ ψ : L →* Y, ∀ l : L,
      ((ψ l : Y) : ↥N ⧸ D.subgroupOf N) = π (Subgroup.inclusion hLN l) :=
    ⟨(π.comp (Subgroup.inclusion hLN)).codRestrict Y hψmem, fun _ => rfl⟩
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hπsurj y
    refine ⟨⟨x, (hmemL x).2 hy⟩, Subtype.ext ?_⟩
    rw [hψ, hincl]
  have hφsurj : Function.Surjective (φY.toMonoidHom.comp ψ) := fun s => by
    obtain ⟨y, rfl⟩ := φY.surjective s
    obtain ⟨l, rfl⟩ := hψsurj y
    exact ⟨l, rfl⟩
  have hφker : (φY.toMonoidHom.comp ψ).ker = D.subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      change φY (ψ l) = 1 at h
      have h1 : ψ l = 1 := (MulEquiv.map_eq_one_iff φY).1 h
      have h2 : π (Subgroup.inclusion hLN l) = 1 := (hψ l).symm.trans (congrArg Subtype.val h1)
      exact (hπ1 _).1 h2
    · intro h
      have h1 : ψ l = 1 := Subtype.ext ((hψ l).trans ((hπ1 _).2 h))
      change φY (ψ l) = 1
      rw [h1, map_one]
  have hψT : (T.subgroupOf L).map ψ = B.subgroupOf Y := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, hB]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨Subgroup.inclusion hLN l, hl, (hψ l).symm⟩
    · rintro ⟨t, ht, hty⟩
      refine ⟨⟨t, hTL ht⟩, ht, Subtype.ext ?_⟩
      rw [hψ, hincl, hty]
  have hφT : (T.subgroupOf L).map (φY.toMonoidHom.comp ψ) =
      CFSG.Timmesfeld.upperUnipotent (GaloisField 2 n) := by
    rw [← Subgroup.map_map, hψT, hφY]
  have hgenL : ∀ a ∈ N, a ∉ Subgroup.normalizer (T : Set G) →
      L = T ⊔ T.map (MulAut.conj a).toMonoidHom := by
    intro a ha haT
    have hBa : B.map (MulAut.conj (π ⟨a, ha⟩)).toMonoidHom ≠ B := fun h =>
      haT (Subgroup.mem_normalizer_iff_map_conj_eq.2 ((hiff ⟨a, ha⟩).1 h))
    have hY := hgen (π ⟨a, ha⟩) hBa
    rw [hconjB, hB, ← Subgroup.map_sup] at hY
    have hcomapY : Y.comap π =
        T.subgroupOf N ⊔ (T.subgroupOf N).map (MulAut.conj (⟨a, ha⟩ : N)).toMonoidHom := by
      rw [← hY, Subgroup.comap_map_eq, hker, sup_eq_left.2 (hKT.trans le_sup_left)]
    rw [hL, hcomapY, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hTN,
      CFSG.Timmesfeld.Bridge.map_subtype_map_conj_subgroupOf hTN]
  exact ⟨L, hDL, hTL, hLN, hNL, ⟨φY.toMonoidHom.comp ψ, hφsurj, hφker, hφT⟩, hgenL⟩

end CFSG.CGT.PushingUpLit.C2L

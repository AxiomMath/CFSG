module

public import CFSG.GH74.Generic.BProg.B2.T4P151V
public import CFSG.GH74.Generic.BProg.B2.Thm2Done
public import CFSG.RankThree.PerfectCover.HopfCentralCovers
public import CFSG.RankThree.PartOne.Q1327C.P5Arith

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.P151W

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup
open CFSG.GH74.Generic.BProg.B2.T4.P151V CFSG.RankThree.PerfectCover
open CFSG.Assembly.LowTwoRank (StatedSU StatedProj)

section Norm

variable {X : Type} [Group X] {L : Subgroup X}

theorem map_conj_eq_of_mem_normalizer {x : X} (hx : x ∈ normalizer (L : Set X)) :
    L.map (MulAut.conj x).toMonoidHom = L := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hx l).1 hl
  · intro hy
    refine ⟨x⁻¹ * y * x, (Subgroup.mem_normalizer_iff.1 hx _).2 ?_, by group⟩
    have : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [this]
    exact hy

theorem mem_normalizer_of_map_conj_eq {x : X} (hx : L.map (MulAut.conj x).toMonoidHom = L) :
    x ∈ normalizer (L : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : (MulAut.conj x).toMonoidHom h ∈ L.map (MulAut.conj x).toMonoidHom := Subgroup.mem_map_of_mem _ hh
    rw [hx] at this
    simpa using this
  · intro hh
    rw [← hx] at hh
    obtain ⟨l, hl, hlh⟩ := hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hlh
    have : l = h := by
      have h1 : x⁻¹ * (x * l * x⁻¹) * x = x⁻¹ * (x * h * x⁻¹) * x := by rw [hlh]
      simpa [mul_assoc] using h1
    rw [← this]
    exact hl

@[expose] noncomputable def normAct (L : Subgroup X) :
    ↥(normalizer (L : Set X)) →* MulAut (↥L ⧸ center ↥L) where
  toFun x := tau (map_conj_eq_of_mem_normalizer x.2)
  map_one' := by
    ext y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    rw [tau_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp [conjL_apply]
  map_mul' x y := by
    ext z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MulAut.mul_apply, tau_mk, tau_mk, tau_mk]
    congr 1
    apply Subtype.ext
    simp only [conjL_apply, Subgroup.coe_mul]
    group

theorem normAct_apply (x : ↥(normalizer (L : Set X))) :
    normAct L x = tau (map_conj_eq_of_mem_normalizer x.2) := rfl

theorem normAct_of_mem (l : ↥L) :
    normAct L ⟨l, Subgroup.le_normalizer l.2⟩ = MulAut.conj (QuotientGroup.mk l : ↥L ⧸ center ↥L) := by
  ext z
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective z
  rw [normAct_apply, tau_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1

theorem inn_le_range_normAct :
    (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).range ≤ (normAct L).range := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨l, Subgroup.le_normalizer l.2⟩, normAct_of_mem l⟩

theorem tau_mem_range_normAct {σ : X} (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) :
    tau hLσ ∈ (normAct L).range :=
  ⟨⟨σ, mem_normalizer_of_map_conj_eq hLσ⟩, rfl⟩

theorem sectional_range_normAct [Finite X] (hG4 : Gen4 X) : SectionalTwoRankLE ↥(normAct L).range 4 :=
  SectionalTwoRankLE.of_surjective (normAct L).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    (SectionalTwoRankLE.subgroup _ hG4)

end Norm

section Restrict

variable {N : Type} [Group N] [Finite N]

theorem shapeInCent_subgroupOf {H : Subgroup N} {t : N} {L : Subgroup N} (hs : ShapeInCent H t L)
    (N' : Subgroup N) (hH : H ≤ N') (ht : t ∈ N') (hL : L ≤ N') :
    ShapeInCent (H.subgroupOf N') ⟨t, ht⟩ (L.subgroupOf N') := by
  have := hs.normal
  refine ⟨inferInstance, ((Subgroup.subgroupOfEquivOfLe hH).isSimpleGroup_congr).2 hs.simple, ?_, ?_, ?_, ?_⟩
  · intro n hn
    apply Subtype.ext
    refine hs.faithful n fun h hh => ?_
    have := hn ⟨h, hH hh⟩ (Subgroup.mem_subgroupOf.2 hh)
    exact congrArg Subtype.val this
  · rw [Subgroup.orderOf_mk]
    exact hs.inv
  · have hmap : ((H.subgroupOf N') ⊓ centralizer ({⟨t, ht⟩} : Set ↥N')).map N'.subtype =
        H ⊓ centralizer ({t} : Set N) := by
      rw [Subgroup.map_inf_eq _ _ _ N'.subtype_injective, Subgroup.subgroupOf_map_subtype,
        B3aG.map_subtype_centralizer, inf_eq_left.2 hH]
      ext z
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hz, -, hz'⟩
        exact ⟨hz, hz'⟩
      · rintro ⟨hz, hz'⟩
        exact ⟨hz, hH hz, hz'⟩
    have hmapL : (L.subgroupOf N').map N'.subtype = L := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hL]
    apply B3aG.isCompIn_of_map_injective N'.subtype_injective
    rw [hmap, hmapL]
    exact hs.comp
  · obtain ⟨Z, hZc, hZo, hZn, hQ⟩ := hs.shape
    set e : ↥(L.subgroupOf N') ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL with he
    have hZ'n : (Z.comap e.toMonoidHom).Normal := hZn.comap _
    have hmapZ : (Z.comap e.toMonoidHom).map e.toMonoidHom = Z :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective Z
    refine ⟨Z.comap e.toMonoidHom, ?_, ?_, hZ'n, ?_⟩
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.1 (hZc (Subgroup.mem_comap.1 hx)) (e g)
    · have h1 : Nat.card ↥((Z.comap e.toMonoidHom).map e.toMonoidHom) = Nat.card ↥(Z.comap e.toMonoidHom) :=
        Nat.card_congr ((Z.comap e.toMonoidHom).equivMapOfInjective _ e.injective).toEquiv.symm
      rw [← h1, hmapZ]
      exact hZo
    · exact QShapeNS.of_mulEquiv (QuotientGroup.congr _ _ e hmapZ).symm hQ

end Restrict

section Refine

theorem puL4_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : PuL4 A) : PuL4 B := by
  obtain ⟨p, f, hp, hp2, hf, h3, ⟨h8, hm⟩ | ⟨h8, hm⟩⟩ := h
  · exact ⟨p, f, hp, hp2, hf, h3, Or.inl ⟨h8, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩
  · exact ⟨p, f, hp, hp2, hf, h3, Or.inr ⟨h8, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩

theorem puL4m_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : PuL4m A) : PuL4m B := by
  obtain ⟨p, f, hp, hp2, hf, h3, ⟨h4, hm⟩ | ⟨h4, hm⟩⟩ := h
  · exact ⟨p, f, hp, hp2, hf, h3, Or.inl ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩
  · exact ⟨p, f, hp, hp2, hf, h3, Or.inr ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {σ : X}


theorem puL4m_of_vert (hG4 : Gen4 X) (hL : IsComponent L) (hσσ : σ * σ = 1)
    (hLσ : L.map (MulAut.conj σ).toMonoidHom = L) (hnt : ∃ l ∈ L, l * σ ≠ σ * l)
    {J : Subgroup X} (hJ : IsCompIn (centralizer ({σ} : Set X)) J) (hJL : J ≤ L)
    (hJT : QShape3 (↥J ⧸ center ↥J)) (hJZ : Odd (Nat.card ↥(center ↥J)))
    (h4 : PuL4 (↥L ⧸ center ↥L)) : PuL4m (↥L ⧸ center ↥L) := by
  have hs := shapeInCent_of_vert hL hσσ hLσ hnt hJ hJL hJT hJZ
  have hHN := inn_le_range_normAct (L := L)
  have hLN : (((J.subgroupOf L).map (QuotientGroup.mk' (center ↥L))).map MulAut.conj) ≤ (normAct L).range :=
    (Subgroup.map_le_range _ _).trans hHN
  have hs' := shapeInCent_subgroupOf hs _ hHN (tau_mem_range_normAct hLσ) hLN
  have hinj : Function.Injective (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)) :=
    GenLocBasic.conj_injective_of_center_trivial (center_trivial_of_component hL)
  set e : (↥L ⧸ center ↥L) ≃* ↥((MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).range.subgroupOf
      (normAct L).range) :=
    (MonoidHom.ofInjective hinj).trans (Subgroup.subgroupOfEquivOfLe hHN).symm with he
  exact puL4m_of_mulEquiv e.symm
    (puL4m_of_gen4_proved _ _ _ hs' (sectional_range_normAct hG4) (puL4_of_mulEquiv e h4))

end Refine

section Gen

@[expose] def GenSect4 (J : Type) [Group J] : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A →
    SectionalTwoRankLE ↥(innJoin α) 4 → gammaAct α = ⊤

theorem GenSect4.of_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J') (h : GenSect4 J) :
    GenSect4 J' := by
  intro A _ _ α' hA hSec
  let α : A →* MulAut J := (MulAut.congr e.symm).toMonoidHom.comp α'
  have hc : ∀ a x, α' a (e x) = e (α a x) := by
    intro a x
    simp [α, MulAut.congr_apply]
  have hSec' : SectionalTwoRankLE ↥(innJoin α) 4 := by
    have heq := GenLocBasic.innJoin_map_congr e α α' hc
    have iso := (innJoin α).equivMapOfInjective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    exact SectionalTwoRankLE.of_mulEquiv ((MulEquiv.subgroupCongr heq).trans iso.symm) hSec
  rw [GenLocBasic.gammaAct_map_equiv e α α' hc, h A α hA hSec', Subgroup.map_top_of_surjective _ e.surjective]

section Lin

variable {F : Type} [Field F] [Finite F]

theorem genSect4_sl4 (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) :
    GenSect4 (Matrix.SpecialLinearGroup (Fin 4) F) :=
  fun _ _ _ α hA hs => gammaAct_sl4_lin hF4 h7 α hA hs

theorem genSect4_psl4 (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) :
    GenSect4 (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F) :=
  fun _ _ _ α hA hs => GenLocL4Lift.gammaAct_projectiveSL4_of_sl4
    (fun α hA hs => gammaAct_sl4_lin hF4 h7 α hA hs) α hA hs

end Lin

theorem pRank_four {L : Type} [Group L] [Finite L] {u₁ u₂ : L} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1)
    (h₁₂ : u₁ * u₂ = u₂ * u₁) (h₁1 : u₁ ≠ 1) (h₂1 : u₂ ≠ 1) (hne : u₁ ≠ u₂) :
    CFSG.IsElementaryAbelian 2 ↥(zpowers u₁ ⊔ zpowers u₂) ∧ pRank 2 ↥(zpowers u₁ ⊔ zpowers u₂) = 2 := by
  have hc₁₂ : ∀ h ∈ zpowers u₁, h * u₂ = u₂ * h := by
    intro h hh
    obtain h' | h' := P151G.mem_zpowers_invol h₁ hh
    · rw [h']; simp
    · rw [h']; exact h₁₂
  have hEel : CFSG.IsElementaryAbelian 2 ↥(zpowers u₁ ⊔ zpowers u₂) :=
    B3.S3Sec29H.isElementaryAbelian_sup_zpowers (P151G.isElementaryAbelian_zpowers_invol h₁) h₂ hc₁₂
  have hE4 : Nat.card ↥(zpowers u₁ ⊔ zpowers u₂) = 4 := P151G.card_four h₁ h₂ h₁₂ h₁1 h₂1 hne
  refine ⟨hEel, ?_⟩
  have h1 := WeakSigGen.card_eq_two_pow_pRank hEel
  rw [hE4] at h1
  have h2 : 2 ^ pRank 2 ↥(zpowers u₁ ⊔ zpowers u₂) = 2 ^ 2 := by rw [← h1]; norm_num
  exact Nat.pow_right_injective (le_refl 2) h2

theorem sup_centralizer_eq_top_of_gammaAct {L : Type} [Group L] [Finite L] {u₁ u₂ : L} (h₁ : u₁ * u₁ = 1)
    (h₂ : u₂ * u₂ = 1) (h₁₂ : u₁ * u₂ = u₂ * u₁) (h₁1 : u₁ ≠ 1) (h₂1 : u₂ ≠ 1) (hne : u₁ ≠ u₂)
    (hZ₁ : u₁ ∉ center L) (hZ₂ : u₂ ∉ center L) (hZ₁₂ : u₁ * u₂ ∉ center L)
    (hγ : gammaAct (ShapeGenS13.conjOn (zpowers u₁ ⊔ zpowers u₂)) = ⊤) :
    centralizer ({u₁} : Set L) ⊔ centralizer ({u₂} : Set L) ⊔ centralizer ({u₁ * u₂} : Set L) = ⊤ := by
  classical
  have hr := (pRank_four h₁ h₂ h₁₂ h₁1 h₂1 hne).2
  have hnc : ∀ E' : Subgroup ↥(zpowers u₁ ⊔ zpowers u₂),
      pRank 2 ↥(zpowers u₁ ⊔ zpowers u₂) - 1 ≤ pRank 2 ↥E' → ∃ b ∈ E', (b : L) ∉ center L := by
    intro E' hE'
    obtain ⟨b, hbE', hb1⟩ := ShapeGenS13.exists_ne_one_of_one_le_pRank (E := E') (by omega)
    refine ⟨b, hbE', ?_⟩
    have hb1' : (b : L) ≠ 1 := fun h => hb1 (Subtype.ext h)
    rcases P151G.mem_four h₁ h₂ h₁₂ b.2 with h | h | h | h
    · exact absurd h hb1'
    · rw [h]; exact hZ₁
    · rw [h]; exact hZ₂
    · rw [h]; exact hZ₁₂
  have hsup := ShapeGenS13.shapeGen_of_gammaAct hnc hγ
  refine eq_top_iff.2 (hsup.symm.le.trans ?_)
  refine iSup₂_le fun b hb => ?_
  obtain ⟨hbE, hbZ⟩ := hb
  rcases P151G.mem_four h₁ h₂ h₁₂ hbE with rfl | rfl | rfl | rfl
  · exact absurd (Subgroup.one_mem _) hbZ
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem sup_centralizer_eq_top_of_genSect4 {L : Type} [Group L] [Finite L] (hS : GenSect4 L)
    (hsect : SectionalTwoRankLE L 4) {u₁ u₂ : L} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1)
    (h₁₂ : u₁ * u₂ = u₂ * u₁) (h₁1 : u₁ ≠ 1) (h₂1 : u₂ ≠ 1) (hne : u₁ ≠ u₂)
    (hZ₁ : u₁ ∉ center L) (hZ₂ : u₂ ∉ center L) (hZ₁₂ : u₁ * u₂ ∉ center L) :
    centralizer ({u₁} : Set L) ⊔ centralizer ({u₂} : Set L) ⊔ centralizer ({u₁ * u₂} : Set L) = ⊤ := by
  set α := ShapeGenS13.conjOn (zpowers u₁ ⊔ zpowers u₂) with hα
  have hle : α.range ≤ (MulAut.conj : L →* MulAut L).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨(b : L), rfl⟩
  have heq : innJoin α = (MulAut.conj : L →* MulAut L).range := sup_eq_left.2 hle
  have hs : SectionalTwoRankLE ↥(innJoin α) 4 :=
    SectionalTwoRankLE.of_mulEquiv (MulEquiv.subgroupCongr heq.symm)
      (SectionalTwoRankLE.of_surjective (MulAut.conj : L →* MulAut L).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _) hsect)
  obtain ⟨hEel, hr⟩ := pRank_four h₁ h₂ h₁₂ h₁1 h₂1 hne
  exact sup_centralizer_eq_top_of_gammaAct h₁ h₂ h₁₂ h₁1 h₂1 hne hZ₁ hZ₂ hZ₁₂
    (hS _ α ⟨hEel, Or.inl hr⟩ hs)

theorem gcd_four_of_mod_four {m : ℕ} (h : m % 4 = 2) : Nat.gcd 4 m = 2 := by
  rw [Nat.gcd_rec, h]
  rfl

theorem card_hopfMultiplier_psl4 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2) (h4 : p ^ f % 4 = 3)
    (hm : CFSG.Models.LieModel Y .PSL 4 p f) : Nat.card (hopfMultiplier Y) = 2 := by
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 4 p f = (Nat.gcd 4 (p ^ f - 1), 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 p f = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [card_hopfMultiplier_of_griess hGA hm, hgen, hexc, gcd_four_of_mod_four (by omega)]
  rfl

theorem card_hopfMultiplier_psu4 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2) (h3 : 3 < p ^ f) (h4 : p ^ f % 4 = 1)
    (hm : CFSG.Models.LieModel Y .PSU 4 p f) : Nat.card (hopfMultiplier Y) = 2 := by
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 4 p f = (Nat.gcd 4 (p ^ f + 1), 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 p f = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [card_hopfMultiplier_of_griess hGA hm, hgen, hexc, gcd_four_of_mod_four (by omega)]
  rfl

theorem sylow_two_card_eq_two {M : Type} [Group M] (h : Nat.card M = 2) : ∀ S : Sylow 2 M, Nat.card S = 2 := by
  have : Finite M := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  rw [Sylow.card_eq_multiplicity, h, Nat.Prime.factorization_self Nat.prime_two, pow_one]

theorem card_eq_two_of_mem_iff {G : Type*} [Group G] {S : Subgroup G} {z : G} (hz : z ≠ 1)
    (h : ∀ g, g ∈ S ↔ g = 1 ∨ g = z) : Nat.card S = 2 := by
  rw [Nat.card_eq_two_iff' (1 : S)]
  refine ⟨⟨z, (h z).2 (Or.inr rfl)⟩, fun h1 => hz (congrArg Subtype.val h1), ?_⟩
  rintro ⟨y, hy⟩ hy1
  rcases (h y).1 hy with rfl | rfl
  · exact absurd rfl hy1
  · rfl

theorem card_center_sl4 {F : Type} [Field F] [Finite F] (hF4 : Nat.card F % 4 = 3) :
    Nat.card ↥(center (Matrix.SpecialLinearGroup (Fin 4) F)) = 2 := by
  obtain ⟨z, hz1, hz, -⟩ := T3S1.Lin.center_lin (F := F) hF4
  have h2 := card_eq_two_of_mem_iff hz1 hz
  rw [← h2]
  exact Nat.card_congr (Subgroup.centerCongr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 F)).toEquiv

theorem card_center_su4 {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : q % 4 = 1) :
    Nat.card ↥(center ↥(StatedSU 4 q K)) = 2 := by
  obtain ⟨F', _, _, -, z, hz⟩ := B1.PilotS1.grpS1_uni hK hq
  have hz1 : z ≠ 1 := by
    intro h1
    have := hz.like.z_ord
    rw [h1, orderOf_one] at this
    omega
  exact card_eq_two_of_mem_iff hz1 hz.center

theorem nonempty_mulEquiv_centerQuot {L : Type} [Group L] (h1 : Nat.card ↥(center L) = 1) :
    Nonempty (L ≃* L ⧸ center L) := by
  have hbot : center L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  refine ⟨MulEquiv.ofBijective (QuotientGroup.mk' (center L)) ⟨?_, QuotientGroup.mk'_surjective _⟩⟩
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hbot]

end Gen

section Uni


theorem genSect4_su4
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) : GenSect4 ↥(StatedSU 4 (p ^ f) K) :=
  fun _ _ _ α hA hs => GenLocU4Fam.su4Gen_of_classes hp hp2 hK hq (thm2Done_extStmt K p f)
    (thm2Done_quatStmt K p f) (thm2Done_outerStmt K p f) α hA hs

theorem genSect4_psu4
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) :
    GenSect4 (StatedProj (StatedSU 4 (p ^ f) K)) :=
  fun _ _ _ α hA hs => GenLocU4Fam.gammaAct_projectiveSU4_of_su4 hp hp2 hK
    (GenLocU4Fam.su4Gen_of_classes hp hp2 hK hq (thm2Done_extStmt K p f) (thm2Done_quatStmt K p f)
      (thm2Done_outerStmt K p f)) α hA hs

theorem genSect4_of_puL4m
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {L : Type} [Group L] [Finite L] (hq : IsQuasisimple L) (h : PuL4m (L ⧸ center L)) : GenSect4 L := by
  have hperf : Group.IsPerfect L := hq.1
  have hd := card_ker_dvd_hopfMultiplier hperf (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  rw [QuotientGroup.ker_mk'] at hd
  obtain ⟨p, f, hp, hp2, -, h3, ⟨h4, hm⟩ | ⟨h4, hm⟩⟩ := h
  · have hM := card_hopfMultiplier_psl4 hGA hp2 h4 (models_of_blueprint_of_ne_zero (by norm_num) hm)
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hm
    have hF4 : Nat.card F % 4 = 3 := by rw [hF]; exact h4
    have h7 : 7 ≤ Nat.card F := by rw [hF]; omega
    rw [hM] at hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · obtain ⟨eL⟩ := nonempty_mulEquiv_centerQuot h1
      exact GenSect4.of_mulEquiv (eL.trans e).symm (genSect4_psl4 hF4 h7)
    · have hqS : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 4) F) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 4 F (by norm_num)
          (Or.inl (by norm_num)) (Or.inl (by norm_num))
      have eS : (Matrix.SpecialLinearGroup (Fin 4) F ⧸ center (Matrix.SpecialLinearGroup (Fin 4) F)) ≃*
          (L ⧸ center L) :=
        (QuotientGroup.quotientMulEquivOfEq
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 F).symm).trans e.symm
      have hSyl := sylow_two_card_eq_two
        ((Nat.card_congr (hopfMultiplierEquivGriess (L ⧸ center L)).toEquiv).trans hM)
      obtain ⟨φ⟩ := (hopf_central_cover_consequences (L ⧸ center L)).2 hSyl L
        (Matrix.SpecialLinearGroup (Fin 4) F) hq hqS h2 (card_center_sl4 hF4) ⟨MulEquiv.refl _⟩ ⟨eS⟩
      exact GenSect4.of_mulEquiv φ.symm (genSect4_sl4 hF4 h7)
  · have hM := card_hopfMultiplier_psu4 hGA hp2 h3 h4 (models_of_blueprint_of_ne_zero (by norm_num) hm)
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GenLocU3.stated_PSU hm
    have : Fact p.Prime := ⟨hp⟩
    rw [hM] at hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · obtain ⟨eL⟩ := nonempty_mulEquiv_centerQuot h1
      exact GenSect4.of_mulEquiv (eL.trans e).symm (genSect4_psu4 hp hp2 hK h4)
    · obtain ⟨hqS, hcen⟩ :=
        CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := 4) hK (by norm_num) (by simp)
      have eS : (↥(StatedSU 4 (p ^ f) K) ⧸ center ↥(StatedSU 4 (p ^ f) K)) ≃* (L ⧸ center L) :=
        (QuotientGroup.quotientMulEquivOfEq hcen).trans e.symm
      have hSyl := sylow_two_card_eq_two
        ((Nat.card_congr (hopfMultiplierEquivGriess (L ⧸ center L)).toEquiv).trans hM)
      obtain ⟨φ⟩ := (hopf_central_cover_consequences (L ⧸ center L)).2 hSyl L ↥(StatedSU 4 (p ^ f) K) hq hqS h2
        (card_center_su4 hK h4) ⟨MulEquiv.refl _⟩ ⟨eS⟩
      exact GenSect4.of_mulEquiv φ.symm (genSect4_su4 hp hp2 hK h4)

theorem vertL4_proved
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : VertL4 := by
  intro X _ _ hG4 _ σ hσ L hL _ hP4 hLσ hnt J hJ hJL hJT hJZ e₁ e₂ he₁ he₂ h₁ h₂ h₁₂ h₁1 h₂1 hne
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hJZo : Odd (Nat.card ↥(center ↥J)) := P151P.odd_card_center_of_noInvol hJZ
  have hm := puL4m_of_vert hG4 hL hσσ hLσ hnt hJ hJL hJT hJZo hP4
  have hS : GenSect4 ↥L := genSect4_of_puL4m hGA hL.1 hm
  have hnc : ∀ (e : X) (he : e ∈ J), e * e = 1 → e ≠ 1 → (⟨e, hJL he⟩ : ↥L) ∉ center ↥L := by
    intro e he hee he1 hc
    refine he1 (hJZ e he (fun l hl => ?_) hee)
    have := Subgroup.mem_center_iff.1 hc ⟨l, hJL hl⟩
    exact (congrArg (fun y : ↥L => (y : X)) this).symm
  have h12sq : (e₁ * e₂) * (e₁ * e₂) = 1 := by
    calc (e₁ * e₂) * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by group
      _ = e₁ * (e₁ * e₂) * e₂ := by rw [h₁₂]
      _ = (e₁ * e₁) * (e₂ * e₂) := by group
      _ = 1 := by rw [h₁, h₂, one_mul]
  have h12ne : e₁ * e₂ ≠ 1 := by
    intro h
    apply hne
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right h₁]
  have htop := sup_centralizer_eq_top_of_genSect4 hS (SectionalTwoRankLE.subgroup L hG4)
    (u₁ := ⟨e₁, hJL he₁⟩) (u₂ := ⟨e₂, hJL he₂⟩) (Subtype.ext h₁) (Subtype.ext h₂) (Subtype.ext h₁₂)
    (fun h => h₁1 (congrArg Subtype.val h)) (fun h => h₂1 (congrArg Subtype.val h))
    (fun h => hne (congrArg Subtype.val h))
    (hnc e₁ he₁ h₁ h₁1) (hnc e₂ he₂ h₂ h₂1) (hnc (e₁ * e₂) (mul_mem he₁ he₂) h12sq h12ne)
  have hle := P151P.le_sup_of_top htop
  exact hle

end Uni

section Orders

open CFSG.Open (ordA ordTwistedA)

theorem sixteen_dvd_card_of_qShape3 {Y : Type} [Group Y] (h : QShape3 Y) : 16 ∣ Nat.card Y := by
  obtain ⟨p, f, hp, hp2, hq, hm⟩ := h
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h8 : 8 ∣ (p ^ f) ^ 2 - 1 := PumpupOutOrders.eight_dvd_sq_sub_one hodd
  have hodd3 : Odd ((p ^ f) ^ 3) := hodd.pow
  have hsub : p ^ f - 1 ∣ (p ^ f) ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow (p ^ f) 1 2
  rcases hm with hm | hm
  · have hA : ordA 2 (p ^ f) = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) / Nat.gcd 3 (p ^ f - 1) := by
      unfold ordA
      rw [show 2 + 1 = 3 from rfl, show 2 * 3 / 2 = 3 from rfl,
        show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by decide)]
    rw [card_of_lieModel_PSL (by norm_num) hm, hA]
    have h2 : 2 ∣ (p ^ f) ^ 3 - 1 := (Nat.Odd.sub_odd hodd3 odd_one).two_dvd
    have hN : 16 ∣ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) :=
      Dvd.dvd.mul_left (by simpa using Nat.mul_dvd_mul h8 h2) _
    have hd : Nat.gcd 3 (p ^ f - 1) ∣ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) :=
      (((Nat.gcd_dvd_right _ _).trans hsub).mul_right _).mul_left _
    have hcop : Nat.Coprime 16 (Nat.gcd 3 (p ^ f - 1)) :=
      Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
    rw [← Nat.div_mul_cancel hd] at hN
    exact hcop.dvd_of_dvd_mul_right hN
  · rw [card_of_lieModel_PSU (by norm_num) hp2 hm]
    have h2 : 2 ∣ (p ^ f) ^ 3 + 1 := (Odd.add_odd hodd3 odd_one).two_dvd
    have hN : 16 ∣ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :=
      Dvd.dvd.mul_left (by simpa using Nat.mul_dvd_mul h8 h2) _
    have hq2 : 2 ≤ p ^ f := by omega
    rw [← CFSG.RankThree.PartOne.Q1327C.ordTwistedA_two_mul (p ^ f) hq2] at hN
    have hcop : Nat.Coprime 16 (Nat.gcd 3 (p ^ f + 1)) :=
      Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
    exact hcop.dvd_of_dvd_mul_right hN

end Orders

theorem puG2_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : PuG2 A) : PuG2 B := by
  obtain ⟨f, hf, hm⟩ := h
  exact ⟨f, hf, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩

section G2


theorem not_qShape3_of_qShape4 {Y : Type} [Group Y] (h3 : QShape3 Y) (h4 : QShape4 Y) : False := by
  obtain ⟨f, hf⟩ := h4
  obtain ⟨k, -, hcard⟩ := card_of_lieModel_twistedG2 hf
  exact PumpupOutOrders.not_sixteen_dvd_ordRee k (hcard ▸ sixteen_dvd_card_of_qShape3 h3)

theorem vertG2_proved : VertG2 := by
  intro X _ _ _ _ σ hσ L hL _ hP hLσ hnt J hJ hJL hJT hJZ _ _ _ _ _ _ _ _ _ _ _
  exfalso
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hJZo : Odd (Nat.card ↥(center ↥J)) := P151P.odd_card_center_of_noInvol hJZ
  have hs := shapeInCent_of_vert hL hσσ hLσ hnt hJ hJL hJT hJZo
  have hinj : Function.Injective (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)) :=
    GenLocBasic.conj_injective_of_center_trivial (center_trivial_of_component hL)
  set eH := MonoidHom.ofInjective hinj with heH
  obtain ⟨f, hf3, hodd, hm⟩ := puG2Odd_of_shape _ _ _ hs (puG2_of_mulEquiv eH hP)
  by_cases hτ : tau hLσ ∈ (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).range
  · exact PumpupTableExc.pumpupIn_g2 3 f Nat.prime_three (by norm_num) (by omega) _ _ _ _ hs hτ hm
  · have hm₀ : CFSG.Blueprint.LieModel (↥L ⧸ center ↥L) .G2 0 3 f :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eH.symm hm
    have h4 := g2_outer_fixed_qShape4 hf3 hodd hm₀ (tau_sq hLσ hσσ) hτ
    have hfix : fixedIn (↥L ⧸ center ↥L) (zpowers (tau hLσ)) = fixTau hLσ := by
      ext y
      rw [GenLocG2Basic.mem_fixedIn_zpowers, mem_fixTau]
    rw [hfix] at h4
    have hsimple : IsSimpleGroup ↥(fixTau hLσ) :=
      PumpupTableTwoInv.isSimpleGroup_of_shape345 (Or.inr (Or.inl h4))
    set Jb := (J.subgroupOf L).map (QuotientGroup.mk' (center ↥L)) with hJb
    have hJc : IsCompIn (fixTau hLσ) Jb := isCompIn_fixTau hLσ hJ hJL
    obtain ⟨⟨eJ⟩, -⟩ := jbar_facts (Prop31.isQuasisimple_of_isCompIn hJ) hJL
    have hQ : QShapeNS (↥Jb ⧸ center ↥Jb) := Or.inr (Or.inl (T4ElimAssembly.qShape3_of_equiv eJ hJT))
    obtain ⟨hEq, hZ, -⟩ := PumpupOutOrders.no_shape_of_simple hJc hsimple le_rfl hQ
    have e1 : (↥Jb ⧸ center ↥Jb) ≃* ↥Jb := (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact not_qShape3_of_qShape4
      (T4ElimAssembly.qShape3_of_equiv ((eJ.trans e1).trans (MulEquiv.subgroupCongr hEq)) hJT) h4

end G2

end CFSG.GH74.Generic.BProg.B2.T4.P151W

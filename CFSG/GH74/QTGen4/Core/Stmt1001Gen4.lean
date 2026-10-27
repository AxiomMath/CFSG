module

public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.EmptyFaithful.S1421QL12Comm
public import CFSG.Quasithin.Background.A3Structure320
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.GH74.QTGen4.Core.CommutingSections

public section

namespace CFSG.GH74.QTGen4

theorem five_or_seven_dvd_card_of_simple {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hnonab : ∃ a b : Y, a * b ≠ b * a) (hd : Nat.card Y ∣ 20160) :
    5 ∣ Nat.card Y ∨ 7 ∣ Nat.card Y := by
  by_contra h
  simp only [not_or] at h
  obtain ⟨h5, h7⟩ := h
  have hc5 : Nat.Coprime (Nat.card Y) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5).symm
  have hc7 : Nat.Coprime (Nat.card Y) 7 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7).symm
  have hd' : Nat.card Y ∣ 2 ^ 6 * 3 ^ 2 := by
    have h20 : (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * (5 * 7) := by norm_num
    rw [h20] at hd
    exact (Nat.Coprime.mul_right hc5 hc7).dvd_of_dvd_mul_right hd
  obtain ⟨k1, k2, hk1, hk2, hk⟩ := Nat.dvd_mul.mp hd'
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk1
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hk2
  have : Fintype Y := Fintype.ofFinite Y
  have hcard : Fintype.card Y = 2 ^ a * 3 ^ b := by
    rw [← Nat.card_eq_fintype_card, hk]
  have hsolv : Group.IsSolvable Y :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      (by norm_num : Nat.Prime 3) (by norm_num) hcard
  obtain ⟨x, y, hxy⟩ := hnonab
  exact hxy ((IsSimpleGroup.comm_iff_isSolvable (G := Y)).mpr hsolv x y)

theorem pCore_le_solvRad_subgroupOf {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    CFSG.pCore 2 ↥K ≤ (CFSG.Quasithin.solvRad K).subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) :=
    IsPGroup.isNilpotent (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
  have hsolv : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := inferInstance
  let N' : Subgroup G := (CFSG.pCore 2 ↥K).map K.subtype
  have hsub : N'.subgroupOf K = CFSG.pCore 2 ↥K := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hN'K : N' ≤ K := Subgroup.map_subtype_le (CFSG.pCore 2 ↥K)
  have hnorm : (N'.subgroupOf K).Normal := by
    rw [hsub]
    exact CFSG.pCore_normal
  have hsolv' : Group.IsSolvable ↥N' :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥K) K.subtype
        K.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥K) K.subtype K.subtype_injective).surjective
  have hle : N' ≤ CFSG.Quasithin.solvRad K :=
    CFSG.Quasithin.le_solvRad hN'K hnorm hsolv'
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  exact hle ⟨x, hx, rfl⟩

theorem center_eq_bot_of_simple {A : Type*} [Group A] [IsSimpleGroup A]
    (hnonab : ∃ a b : A, a * b ≠ b * a) : Subgroup.center A = ⊥ := by
  have : (Subgroup.center A).Normal := (Subgroup.center A).normal_of_characteristic
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ Subgroup.center A := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem inv_mul_comm_mem_solvRad {G : Type} [Group G] [Finite G] {H K L M : Subgroup G}
    (hKH : K ≤ H) (hLK : L ≤ K) (hMK : M ≤ K) (hcomm : ⁅M, L⁆ ≤ CFSG.Quasithin.solvRad H) {x y : G}
    (hx : x ∈ L) (hy : y ∈ M) : (x * y)⁻¹ * (y * x) ∈ CFSG.Quasithin.solvRad K := by
  have h1 := Subgroup.commutator_mem_commutator (M.inv_mem hy) (L.inv_mem hx)
  have h2 : y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ ∈ K := by
    simp only [inv_inv]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem (hMK hy)) (K.inv_mem (hLK hx)))
      (hMK hy)) (hLK hx)
  have h3 : y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ ∈ CFSG.Quasithin.solvRad K :=
    CFSG.Quasithin.inf_solvRad_le_solvRad hKH ⟨h2, hcomm h1⟩
  have heq : (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by
    group
  rw [heq]
  exact h3

def mkHom {G : Type} [Group G] {K L : Subgroup G} (N : Subgroup K) [N.Normal] (h : L ≤ K) :
    L →* K ⧸ N :=
  (QuotientGroup.mk' N).comp (Subgroup.inclusion h)

theorem commute_images {G : Type} [Group G] {K L M R : Subgroup G} [(R.subgroupOf K).Normal]
    (hLK : L ≤ K) (hMK : M ≤ K)
    (h : ∀ x ∈ L, ∀ y ∈ M, (x * y)⁻¹ * (y * x) ∈ R) :
    ∀ a ∈ (mkHom (R.subgroupOf K) hLK).range, ∀ b ∈ (mkHom (R.subgroupOf K) hMK).range,
      a * b = b * a := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  simp only [mkHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using h x x.2 y y.2

instance solvRad_subgroupOf_normal {G : Type} [Group G] (H : Subgroup G) :
    ((CFSG.Quasithin.solvRad H).subgroupOf H).Normal :=
  CFSG.Quasithin.solvRad_normal H

theorem inf_solvRad_eq_solvRad {G : Type} [Group G] [Finite G] {L K : Subgroup G}
    (hLK : L ≤ K) (hKN : K ≤ Subgroup.normalizer (L : Set G)) :
    L ⊓ CFSG.Quasithin.solvRad K = CFSG.Quasithin.solvRad L := by
  apply le_antisymm
  · exact CFSG.Quasithin.inf_solvRad_le_solvRad hLK
  · refine le_inf (CFSG.Quasithin.solvRad_le L) ?_
    have hs : Group.IsSolvable ↥(CFSG.Quasithin.solvRad L) :=
      CFSG.Quasithin.solvRad_isSolvable L
    have hle : CFSG.Quasithin.solvRad L ≤ K := (CFSG.Quasithin.solvRad_le L).trans hLK
    have hn : ((CFSG.Quasithin.solvRad L).subgroupOf K).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact CFSG.Quasithin.conj_mem_solvRad (hKN g.2) hn
    exact CFSG.Quasithin.le_solvRad hle hn hs

theorem range_props {G : Type} [Group G] [Finite G] {X K L : Subgroup G}
    (hL : L ∈ CFSG.Quasithin.cComp X)
    (hLK : L ≤ K) (hKN : K ≤ Subgroup.normalizer (L : Set G)) :
    IsSimpleGroup ↥(mkHom ((CFSG.Quasithin.solvRad K).subgroupOf K) hLK).range ∧
    (∃ a b : ↥(mkHom ((CFSG.Quasithin.solvRad K).subgroupOf K) hLK).range, a * b ≠ b * a) ∧
    Nat.card ↥(mkHom ((CFSG.Quasithin.solvRad K).subgroupOf K) hLK).range =
      (CFSG.Quasithin.solvRad L).relIndex L := by
  have heq := inf_solvRad_eq_solvRad hLK hKN
  have hker : (mkHom ((CFSG.Quasithin.solvRad K).subgroupOf K) hLK).ker =
      (CFSG.Quasithin.solvRad L).subgroupOf L := by
    ext x
    have hmem : ((x : L) : G) ∈ CFSG.Quasithin.solvRad L ↔
        ((x : L) : G) ∈ CFSG.Quasithin.solvRad K := by
      rw [← heq]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hmem]
    simp [mkHom, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let e : ↥(mkHom ((CFSG.Quasithin.solvRad K).subgroupOf K) hLK).range ≃*
      ↥L ⧸ (CFSG.Quasithin.solvRad L).subgroupOf L :=
    (QuotientGroup.quotientKerEquivRange _).symm.trans (QuotientGroup.quotientMulEquivOfEq hker)
  obtain ⟨-, ⟨hsimp, hnonab⟩, -⟩ := CFSG.Quasithin.cComp_structure hL
  have hsimpA : IsSimpleGroup ↥(mkHom ((CFSG.Quasithin.solvRad K).subgroupOf K) hLK).range := by
    have := hsimp
    exact e.isSimpleGroup
  refine ⟨hsimpA, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h' := congrArg e h
    simpa using h'
  · rw [Nat.card_congr e.toEquiv]
    rfl

theorem solvRad_conj_eq {G : Type} [Group G] [Finite G] (L : Subgroup G) (t : G) :
    CFSG.Quasithin.solvRad (CFSG.Quasithin.conjSub t L) =
      (CFSG.Quasithin.solvRad L).map (MulAut.conj t).toMonoidHom := by
  unfold CFSG.Quasithin.conjSub
  have h1 := CFSG.Quasithin.A320.map_solvRad_le (MulAut.conj t).toMonoidHom L
  have hcomp : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      MonoidHom.id G := by
    ext x
    show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x
    group
  have hgf : (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom = L := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have h2 : (CFSG.Quasithin.solvRad (L.map (MulAut.conj t).toMonoidHom)).map
      (MulAut.conj t⁻¹).toMonoidHom ≤ CFSG.Quasithin.solvRad L := by
    have h := CFSG.Quasithin.A320.map_solvRad_le (MulAut.conj t⁻¹).toMonoidHom
      (L.map (MulAut.conj t).toMonoidHom)
    rwa [hgf] at h
  refine le_antisymm ?_ h1
  intro x hx
  have hgx : (MulAut.conj t⁻¹).toMonoidHom x ∈ CFSG.Quasithin.solvRad L := h2 ⟨x, hx, rfl⟩
  refine ⟨(MulAut.conj t⁻¹).toMonoidHom x, hgx, ?_⟩
  show t * (t⁻¹ * x * t⁻¹⁻¹) * t⁻¹ = x
  group

theorem relIndex_solvRad_conj {G : Type} [Group G] [Finite G] (L : Subgroup G) (t : G) :
    (CFSG.Quasithin.solvRad (CFSG.Quasithin.conjSub t L)).relIndex
        (CFSG.Quasithin.conjSub t L) =
      (CFSG.Quasithin.solvRad L).relIndex L := by
  have hinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  rw [solvRad_conj_eq, CFSG.Quasithin.conjSub, Subgroup.relIndex_map_map_of_injective _ _ hinj]

theorem ne_conjSub_of_not_mem_normalizer {G : Type} [Group G] {L : Subgroup G} {t : G}
    (ht : t ∉ Subgroup.normalizer (L : Set G)) : CFSG.Quasithin.conjSub t L ≠ L := by
  intro h
  apply ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hx : ∀ y : G, y ∈ CFSG.Quasithin.conjSub t L ↔ t⁻¹ * y * t ∈ L :=
    fun y => CFSG.Quasithin.mem_conjSub
  rw [h] at hx
  have h' := hx (t * x * t⁻¹)
  rw [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at h'
  exact h'.symm

theorem false_of_commuting {X : Type} [Group X] [Finite X] {A B : Subgroup X}
    [IsSimpleGroup ↥A] (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hnA : ∃ a b : ↥A, a * b ≠ b * a)
    (hX : Nat.card X ∣ 20160) (hcard : Nat.card ↥B = Nat.card ↥A) : False := by
  have hZ : Subgroup.center ↥A = ⊥ := center_eq_bot_of_simple hnA
  have hdA : Nat.card ↥A ∣ 20160 := (Subgroup.card_subgroup_dvd_card A).trans hX
  rcases five_or_seven_dvd_card_of_simple hnA hdA with h5 | h7
  · have hsq := sq_dvd_card_of_commute hAB hZ (by norm_num : Nat.Prime 5) h5
      (by rw [hcard]; exact h5)
    exact absurd (hsq.trans hX) (by norm_num)
  · have hsq := sq_dvd_card_of_commute hAB hZ (by norm_num : Nat.Prime 7) h7
      (by rw [hcard]; exact h7)
    exact absurd (hsq.trans hX) (by norm_num)

theorem stmt10_0_1_gen4 :
    ∀ (G : Type) [Group G] [Finite G], CFSG.GH74.Gen4 G →
      ∀ (T L : Subgroup G), IsSimpleGroup G →
      (∃ a b : G, a * b ≠ b * a) → CFSG.QuasithinUnique.quasithinIsQTKECat G →
      CFSG.Open.quasithinIsSylowTwo T → CFSG.Open.quasithinIsMaximalLocal T L →
      CFSG.Open.quasithinIsFaithfulLocal T L →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) := by
  intro G _ _ hG T L _hsimple _hnonab hqtke hsyl _hmax hfaith _hqs
  by_contra hT
  have hex : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    apply hT
    intro t ht
    by_contra htN
    exact h ⟨t, ht, htN⟩
  obtain ⟨t, ht, htN⟩ := hex
  obtain ⟨S, rfl⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hsyl
  have hfl := hfaith.1
  have hL0 : L ∈ CFSG.Quasithin.cComp (L ⊔ (S : Subgroup G)) :=
    CFSG.Quasithin.mem_cComp_iff.mpr hfl.2.1
  have hInH : CFSG.Quasithin.InH (S : Subgroup G) (L ⊔ (S : Subgroup G)) := by
    unfold CFSG.Quasithin.InH
    exact ⟨le_sup_right, hfl.2.2.2⟩
  have hTH : (S : Subgroup G) ≤ L ⊔ (S : Subgroup G) := le_sup_right
  have hM0 : CFSG.Quasithin.conjSub t L ∈ CFSG.Quasithin.cComp (L ⊔ (S : Subgroup G)) :=
    CFSG.Quasithin.conjSub_mem_cComp_of_mem hL0 (hTH ht)
  have hMne : CFSG.Quasithin.conjSub t L ≠ L := ne_conjSub_of_not_mem_normalizer htN
  have hcomm : ⁅CFSG.Quasithin.conjSub t L, L⁆ ≤
      CFSG.Quasithin.solvRad (L ⊔ (S : Subgroup G)) :=
    CFSG.Quasithin.commutator_le_solvRad_of_ne hM0 hL0 hMne
  set H₀ : Subgroup G := L ⊔ (S : Subgroup G) with hH₀
  set M : Subgroup G := CFSG.Quasithin.conjSub t L with hMdef
  set K : Subgroup G := L ⊔ M with hKdef
  have hLH : L ≤ H₀ := le_sup_left
  have hMH : M ≤ H₀ := CFSG.Quasithin.le_of_mem_cComp hM0
  have hKH : K ≤ H₀ := sup_le hLH hMH
  have hLK : L ≤ K := le_sup_left
  have hMK : M ≤ K := le_sup_right
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hMN : M ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.Quasithin.H13.LocDbl.le_normalizer_of_mem_cComp hL0 hM0
  have hLN' : L ≤ Subgroup.normalizer (M : Set G) :=
    CFSG.Quasithin.H13.LocDbl.le_normalizer_of_mem_cComp hM0 hL0
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := sup_le hLN hMN
  have hKN' : K ≤ Subgroup.normalizer (M : Set G) := sup_le hLN' Subgroup.le_normalizer
  have hcommK : ∀ x ∈ L, ∀ y ∈ M, (x * y)⁻¹ * (y * x) ∈ CFSG.Quasithin.solvRad K :=
    fun x hx y hy => inv_mul_comm_mem_solvRad hKH hLK hMK hcomm hx hy
  have hAB := commute_images (R := CFSG.Quasithin.solvRad K) hLK hMK hcommK
  obtain ⟨hsA, hnA, hcA⟩ := range_props hL0 hLK hKN
  obtain ⟨hsB, -, hcB⟩ := range_props hM0 hMK hKN'
  have hcard : Nat.card ↥(mkHom ((CFSG.Quasithin.solvRad K).subgroupOf K) hMK).range =
      Nat.card ↥(mkHom ((CFSG.Quasithin.solvRad K).subgroupOf K) hLK).range := by
    rw [hcA, hcB]
    exact relIndex_solvRad_conj L t
  have hXdvd : Nat.card (↥K ⧸ (CFSG.Quasithin.solvRad K).subgroupOf K) ∣ 20160 := by
    have h1 := Subgroup.index_dvd_of_le (pCore_le_solvRad_subgroupOf K)
    have h2 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ 20160 :=
      modO2_dvd_of_inH hG hqtke.2.1 S hInH hKH
    exact h1.trans h2
  have := hsA
  exact false_of_commuting hAB hnA hXdvd hcard

end CFSG.GH74.QTGen4

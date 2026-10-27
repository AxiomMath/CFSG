module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3A6CubeN
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Out
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexOrbit
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_ne_one_of_card_center_eq_three {Q : Type*} [Group Q]
    (hZ : Nat.card (Subgroup.center Q) = 3) :
    ∃ ζ ∈ Subgroup.center Q, ζ ≠ 1 ∧ orderOf ζ ∣ 3 := by
  have hne : Subgroup.center Q ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hZ; omega
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨x, x.2, fun h => hx (Subtype.ext h), ?_⟩
  have := Subgroup.orderOf_dvd_natCard (Subgroup.center Q) x.2
  rwa [hZ] at this

theorem false_of_card_center_eq_three_of_alt {Q : Type*} [Group Q]
    (hZ : Nat.card (Subgroup.center Q) = 3) {m : ℕ} (hm : m ≠ 3)
    (e : Q ≃* alternatingGroup (Fin m)) : False := by
  obtain ⟨ζ, hζ, hζ1, -⟩ := exists_ne_one_of_card_center_eq_three hZ
  apply hζ1
  rw [← e.map_eq_one_iff]
  rcases Nat.lt_or_ge m 3 with h | h
  · have hbot := alternatingGroup.eq_bot_of_card_le_two (α := Fin m) (by simp; omega)
    exact Subtype.ext (Subgroup.mem_bot.mp (hbot.le (e ζ).2))
  · have hcen : e ζ ∈ Subgroup.center (alternatingGroup (Fin m)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hζ q)]
    rw [alternatingGroup.center_eq_bot (by simp; omega)] at hcen
    exact Subgroup.mem_bot.mp hcen

theorem eq_three_of_card_alternatingGroup {n : ℕ}
    (h : Nat.card (alternatingGroup (Fin (2 * n))) = 360) : n = 3 := by
  rcases n with _ | n
  · rw [alternatingGroup.eq_bot_of_card_le_two (by simp), Subgroup.card_bot] at h
    omega
  · have : Nontrivial (Fin (2 * (n + 1))) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin] at h
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp_all [Nat.factorial]
    · have := Nat.factorial_le (show 8 ≤ 2 * (n + 1) by omega)
      have h8 : Nat.factorial 8 = 40320 := by decide
      omega

theorem perm_three_center (g : Equiv.Perm (Fin 3)) (hg : ∀ h, g * h = h * g) : g = 1 := by
  revert g; decide

theorem false_of_center_le_of_perm_three {Γ : Type*} [Group Γ] {Y J : Subgroup Γ}
    (hJY : J ≤ Y) (hZ : Nat.card (Subgroup.center Y) = 3)
    (hZJ : ∀ ζ ∈ Subgroup.center Y, (ζ : Γ) ∈ J)
    (ψ : J →* Equiv.Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (hker : ∀ j, ψ j = 1 → ∃ k : ℕ, j ^ (2 ^ k) = 1) : False := by
  obtain ⟨ζ, hζ, hζ1, h3⟩ := exists_ne_one_of_card_center_eq_three hZ
  set j : J := ⟨ζ, hZJ ζ hζ⟩
  have hcen : ψ j = 1 := perm_three_center _ fun σ => by
    obtain ⟨k, rfl⟩ := hψ σ
    rw [← map_mul, ← map_mul]
    congr 1
    have := Subgroup.mem_center_iff.mp hζ ⟨k, hJY k.2⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val this.symm)
  obtain ⟨k, hk⟩ := hker j hcen
  have hjo : orderOf j = orderOf ζ := by
    rw [← Subgroup.orderOf_coe j, ← Subgroup.orderOf_coe ζ]
  have hdvd : orderOf ζ ∣ 2 ^ k := hjo ▸ orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf ζ) (2 ^ k) :=
    Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_right k (by norm_num))
  exact hζ1 (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd))

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have : Nontrivial (Fin 6) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem false_of_alt6 {K V : Subgroup (alternatingGroup (Fin 6))}
    (hK : ¬ 2 ∣ K.index) (hKt : K ≠ ⊤) (hV : 9 ∣ Nat.card V)
    (hVK : V ≤ Subgroup.normalizer (K : Set (alternatingGroup (Fin 6)))) : False := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hc := card_alt6
  set W := K ⊔ V with hW
  have hWK : W.index ∣ K.index := Subgroup.index_dvd_of_le le_sup_left
  have hWV : W.index ∣ V.index := Subgroup.index_dvd_of_le le_sup_right
  have hVi : V.index ∣ 40 := by
    have h1 := V.card_mul_index
    rw [hc] at h1
    obtain ⟨a, ha⟩ := hV
    rw [ha] at h1
    exact ⟨a, by
      have : 9 * (a * V.index) = 9 * 40 := by rw [← mul_assoc, h1]
      have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
      rw [← this, mul_comm]⟩
  have hW40 : W.index ∣ 40 := hWV.trans hVi
  have hWodd : ¬ 2 ∣ W.index := fun h2 => hK (h2.trans hWK)
  have hpos : 0 < W.index := Nat.pos_of_dvd_of_pos hW40 (by norm_num)
  have hle : W.index ≤ 40 := Nat.le_of_dvd (by norm_num) hW40
  have hbot : (⊥ : Subgroup (alternatingGroup (Fin 6))).index = 360 := by
    rw [Subgroup.index_bot, hc]
  have h15 : W.index = 1 ∨ W.index = 5 := by
    interval_cases h : W.index <;> omega
  rcases h15 with h1 | h5
  · have hWt : W = ⊤ := Subgroup.index_eq_one.mp h1
    have hN : Subgroup.normalizer (K : Set (alternatingGroup (Fin 6))) = ⊤ :=
      top_le_iff.mp (hWt ▸ sup_le Subgroup.le_normalizer hVK)
    have : K.Normal := Subgroup.normalizer_eq_top_iff.mp hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hb | ht
    · rw [hb, hbot] at hK; exact hK ⟨180, rfl⟩
    · exact hKt ht
  · have : W.normalCore.Normal := Subgroup.normalCore_normal W
    have hcore := Subgroup.index_normalCore_le_factorial_index W
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W.normalCore with hb | ht
    · rw [hb, hbot, h5] at hcore
      exact absurd hcore (by decide)
    · have : W = ⊤ := top_le_iff.mp (ht ▸ Subgroup.normalCore_le W)
      rw [this, Subgroup.index_top] at h5
      omega

section Core

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem mk_eq_of_dec {Y : Subgroup Γ} {u l l' : Γ} (hl : l ∈ Y) (hl' : l' ∈ Y)
    (hc : l⁻¹ * u ∈ Subgroup.centralizer (Y : Set Γ))
    (hc' : l'⁻¹ * u ∈ Subgroup.centralizer (Y : Set Γ)) :
    (QuotientGroup.mk' (Subgroup.center Y) ⟨l, hl⟩ : Y ⧸ Subgroup.center Y) =
      QuotientGroup.mk' (Subgroup.center Y) ⟨l', hl'⟩ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_center_iff]
  intro g
  have hm : l⁻¹ * l' ∈ Subgroup.centralizer (Y : Set Γ) := by
    have := (Subgroup.centralizer (Y : Set Γ)).mul_mem hc
      ((Subgroup.centralizer (Y : Set Γ)).inv_mem hc')
    simpa [mul_assoc] using this
  exact Subtype.ext (by simpa using Subgroup.mem_centralizer_iff.mp hm g g.2)

omit [Finite Γ] in
theorem exists_dec_hom {Y U : Subgroup Γ}
    (hdec : ∀ u ∈ U, ∃ l ∈ Y, l⁻¹ * u ∈ Subgroup.centralizer (Y : Set Γ)) :
    ∃ θ : U →* Y ⧸ Subgroup.center Y,
      (∀ u : U, ∀ l (hl : l ∈ Y), l⁻¹ * (u : Γ) ∈ Subgroup.centralizer (Y : Set Γ) →
        θ u = QuotientGroup.mk' (Subgroup.center Y) ⟨l, hl⟩) ∧
      ∀ u : U, θ u = 1 ↔ (u : Γ) ∈ Subgroup.centralizer (Y : Set Γ) := by
  classical
  choose l hlY hlc using hdec
  set C := Subgroup.centralizer (Y : Set Γ)
  let f : U → Y ⧸ Subgroup.center Y := fun u =>
    QuotientGroup.mk' (Subgroup.center Y) ⟨l u u.2, hlY u u.2⟩
  have hf : ∀ u : U, ∀ l' (hl' : l' ∈ Y), l'⁻¹ * (u : Γ) ∈ C →
      f u = QuotientGroup.mk' (Subgroup.center Y) ⟨l', hl'⟩ := fun u l' hl' hc' =>
    mk_eq_of_dec (hlY u u.2) hl' (hlc u u.2) hc'
  have hmul : ∀ a b : U, f (a * b) = f a * f b := by
    intro a b
    set la := l a a.2
    set lb := l b b.2
    have hca : la⁻¹ * (a : Γ) ∈ C := hlc a a.2
    have hcb : lb⁻¹ * (b : Γ) ∈ C := hlc b b.2
    have hcomm : lb⁻¹ * (la⁻¹ * (a : Γ)) = (la⁻¹ * (a : Γ)) * lb⁻¹ :=
      Subgroup.mem_centralizer_iff.mp hca lb⁻¹ (Y.inv_mem (hlY b b.2))
    have he : (la * lb)⁻¹ * ((a * b : U) : Γ) = (la⁻¹ * (a : Γ)) * (lb⁻¹ * (b : Γ)) := by
      calc (la * lb)⁻¹ * ((a * b : U) : Γ) = (lb⁻¹ * (la⁻¹ * (a : Γ))) * (b : Γ) := by
            simp [mul_assoc]
        _ = ((la⁻¹ * (a : Γ)) * lb⁻¹) * (b : Γ) := by rw [hcomm]
        _ = _ := by simp [mul_assoc]
    rw [hf (a * b) (la * lb) (Y.mul_mem (hlY a a.2) (hlY b b.2)) (he ▸ C.mul_mem hca hcb)]
    rfl
  have hone : f 1 = 1 := by
    rw [hf 1 1 Y.one_mem (by simp)]
    rfl
  refine ⟨⟨⟨f, hone⟩, hmul⟩, hf, fun u => ?_⟩
  change f u = 1 ↔ _
  constructor
  · intro h1
    have hz : (⟨l u u.2, hlY u u.2⟩ : Y) ∈ Subgroup.center Y := by
      have : QuotientGroup.mk' (Subgroup.center Y) ⟨l u u.2, hlY u u.2⟩ = 1 := h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hlC : l u u.2 ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
      simpa using congrArg Subtype.val this
    have := C.mul_mem hlC (hlc u u.2)
    simpa using this
  · intro hu
    rw [hf u 1 Y.one_mem (by simpa using hu)]
    rfl

theorem index_centralizer_le_three {Y J U : Subgroup Γ}
    (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 6))
    (hJY : J ≤ Y) (hZJ : ∀ ζ ∈ Subgroup.center Y, (ζ : Γ) ∈ J) (hJne : J ≠ Y)
    {T : Subgroup Γ} (hT : IsSylowTwoOf T Y) (hTJ : T ≤ J)
    (hU3 : IsPGroup 3 U) (hUJ : U ≤ Subgroup.normalizer (J : Set Γ))
    (hdec : ∀ u ∈ U, ∃ l ∈ Y, l⁻¹ * u ∈ Subgroup.centralizer (Y : Set Γ)) :
    ((U ⊓ Subgroup.centralizer (Y : Set Γ)).subgroupOf U).index ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨θ, hθ, hker⟩ := exists_dec_hom hdec
  set C := Subgroup.centralizer (Y : Set Γ)
  set π := QuotientGroup.mk' (Subgroup.center Y)
  have hkθ : θ.ker = (U ⊓ C).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
  rw [← hkθ, Subgroup.index_ker]
  set J' := J.subgroupOf Y
  set K := (J'.map π).map e.toMonoidHom
  set V := θ.range.map e.toMonoidHom
  have hcardV : Nat.card V = Nat.card θ.range :=
    Subgroup.card_map_of_injective (show Function.Injective e.toMonoidHom from e.injective)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).mp
    (hU3.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective)
  rw [hk]
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp_all
  have h9 : 9 ∣ Nat.card V := by
    rw [hcardV, hk]
    exact (pow_dvd_pow 3 hk2 : 3 ^ 2 ∣ 3 ^ k)
  have hKodd : ¬ 2 ∣ K.index := by
    have h1 : K.index ∣ (J'.map π).index :=
      Subgroup.index_map_dvd _ e.surjective
    have h2 : (J'.map π).index ∣ J'.index :=
      Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
    have h3 : J'.index ∣ (T.subgroupOf Y).index :=
      Subgroup.index_dvd_of_le fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hTJ (Subgroup.mem_subgroupOf.mp hx))
    exact fun h => hT.2.2 (h.trans (h1.trans (h2.trans h3)))
  have hKt : K ≠ ⊤ := by
    intro hK
    have hm : J'.map π = ⊤ := by
      have := Subgroup.comap_map_eq_self_of_injective
        (show Function.Injective e.toMonoidHom from e.injective) (J'.map π)
      rw [← this]
      change Subgroup.comap e.toMonoidHom K = ⊤
      rw [hK, Subgroup.comap_top]
    have hker' : π.ker ≤ J' := by
      rw [QuotientGroup.ker_mk']
      intro ζ hζ
      exact Subgroup.mem_subgroupOf.mpr (hZJ ζ hζ)
    have hJ't : J' = ⊤ := by
      rw [← Subgroup.comap_map_eq_self hker', hm, Subgroup.comap_top]
    apply hJne
    refine le_antisymm hJY fun y hy => ?_
    have : (⟨y, hy⟩ : Y) ∈ J' := hJ't ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hVK : V ≤ Subgroup.normalizer (K : Set (alternatingGroup (Fin 6))) := by
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map e.toMonoidHom)
    rintro _ ⟨u, rfl⟩
    obtain ⟨l, hlY, hlc⟩ := hdec u u.2
    rw [hθ u l hlY hlc]
    refine Subgroup.le_normalizer_map π ⟨⟨l, hlY⟩, ?_, rfl⟩
    have hlN : l ∈ Subgroup.normalizer (J : Set Γ) := by
      have hcN : l⁻¹ * (u : Γ) ∈ Subgroup.normalizer (J : Set Γ) :=
        Subgroup.mem_normalizer_fintype fun j hj => by
          have := Subgroup.mem_centralizer_iff.mp hlc j (hJY hj)
          rw [← this]
          simpa [mul_assoc] using hj
      have := (Subgroup.normalizer (J : Set Γ)).mul_mem (hUJ u.2)
        ((Subgroup.normalizer (J : Set Γ)).inv_mem hcN)
      simpa using this
    show (⟨l, hlY⟩ : Y) ∈ Subgroup.normalizer (J' : Set Y)
    rw [Subgroup.mem_normalizer_iff]
    intro j
    simp only [J', Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp hlN) j
  exact false_of_alt6 hKodd hKt h9 hVK

end Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_mem_barM {M X : Subgroup G} (m : M) (hm : (m : G) ∈ X) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ∈ barM M X :=
  ⟨m, hm, rfl⟩

theorem prop3 {p : ℕ} {P : Sylow p G} {M H R : Subgroup G} (h : D1PhaseThree p P M H R)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hc : CenterCentralizesBlockV M (pCoreOf 2 H) L hL.le) (hns : ¬ IsShort2 L) :
    (∀ ζ ∈ Subgroup.center ↥(barM M L),
        (ζ : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ∧
      barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠ barM M L ∧
      NineThreeTwo M (pCoreOf 2 H) L ∧
      ¬ IsSylowTwoOf (barM M (pCoreOf 2 H ⊓ L)) (barM M L) := by
  set S := pCoreOf 2 H
  have hVf := h.blockV_facts h86 hL
  have hHN : H ≤ Subgroup.normalizer (S : Set G) := localGroup_le_normalizer_pCoreOf 2 H
  have hQS : pCoreOf 2 M ≤ S := h.toD1Escape.twoCore_M_le h.twoCore_inf
  have hi : ∀ ζ ∈ Subgroup.center ↥(barM M L),
      (ζ : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
    intro ζ hζ
    obtain ⟨m, hm, hmζ⟩ := ζ.2
    have hmL : (m : G) ∈ L := hm
    have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hL.le hmL⟩ ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_center_iff.mp hζ ⟨y, hy⟩
      have e : (⟨(m : G), hL.le hmL⟩ : M) = m := rfl
      rw [e, hmζ]
      simpa using congrArg Subtype.val this
    have hcV : (m : G) ∈ Subgroup.centralizer (blockV S L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hc (m : G) hmL hcen v hv).symm
    have hmH : (m : G) ∈ H := (hVf.2.2.2 ⟨Subgroup.mem_sup_left hmL, hcV⟩).1
    rw [← hmζ]
    exact mk_mem_barM m ⟨hHN hmH, hmL⟩
  have hJ : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≠ barM M L := by
    intro hJ
    apply hL.not_le_normalizer
    intro l hl
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hL.le hl⟩ ∈
        barM M (Subgroup.normalizer (S : Set G) ⊓ L) := hJ ▸ mk_mem_barM _ hl
    obtain ⟨m, hm, hmeq⟩ := hmem
    have hq : m⁻¹ * ⟨l, hL.le hl⟩ ∈ CFSG.pCore 2 ↥M := QuotientGroup.eq.mp hmeq
    have hqS : ((m⁻¹ * ⟨l, hL.le hl⟩ : M) : G) ∈ S := hQS ⟨_, hq, rfl⟩
    have hlm : l = (m : G) * ((m⁻¹ * ⟨l, hL.le hl⟩ : M) : G) := by simp
    rw [hlm]
    exact (Subgroup.normalizer (S : Set G)).mul_mem (Subgroup.mem_inf.mp hm).1
      (Subgroup.le_normalizer hqS)
  have h2 : NineThreeTwo M S L := by
    rcases h.nineThree h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · exact (hns h1.1).elim
    · exact h2
    · exact (hns h3.1).elim
    · exact (hns h4.1).elim
    · exact (hns h5.1).elim
    · exfalso
      obtain ⟨-, n, ⟨e1⟩, ⟨e2⟩⟩ := h6
      obtain ⟨e0⟩ := hA6
      have hcard : Nat.card (alternatingGroup (Fin (2 * n))) = 360 := by
        rw [← Nat.card_congr e1.toEquiv, Nat.card_congr e0.toEquiv]
        have : Nontrivial (Fin 6) := Fin.nontrivial_iff_two_le.mpr (by omega)
        rw [nat_card_alternatingGroup, Nat.card_fin]
        decide
      have hn := eq_three_of_card_alternatingGroup hcard
      subst hn
      set J := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
      have hJL : J ≤ barM M L := Subgroup.map_mono fun x hx => (Subgroup.mem_subgroupOf.mp hx).2
      refine false_of_center_le_of_perm_three hJL hZ hi
        (e2.toMonoidHom.comp (QuotientGroup.mk' _))
        (e2.surjective.comp (QuotientGroup.mk'_surjective _)) fun j hj => ?_
      have hj1 : QuotientGroup.mk' (CFSG.pCore 2 ↥J) j = 1 := e2.map_eq_one_iff.mp hj
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hj1
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨j, hj1⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exfalso
      obtain ⟨-, n, ⟨e⟩, -⟩ := h7
      exact false_of_card_center_eq_three_of_alt hZ (by omega) e
    · exact (hns h8.1).elim
  exact ⟨hi, hJ, h2, (h.nineThree_not_one h85 hD2 hL).2 h2⟩

theorem index_centralizer_barM_le_three {P : Sylow 3 G} {M H R : Subgroup G}
    (h : D1PhaseThree 3 P M H R) (hThree : KFactBlockThreeASix)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hc : CenterCentralizesBlockV M (pCoreOf 2 H) L hL.le) (hns : ¬ IsShort2 L)
    (hRP : R ≤ (P : Subgroup G)) :
    ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp
        (Subgroup.inclusion (hRP.trans h.toD1Escape.sylow_le)))).index ≤ 3 := by
  have hPM : (P : Subgroup G) ≤ M := h.toD1Escape.sylow_le
  obtain ⟨hi, hJne, h2, -⟩ := prop3 h h85 h86 h93 hD2 hL hZ hA6 hc hns
  obtain ⟨-, hdec⟩ := h.dec_of_threeASix hThree hcyc hzM hz3 hCz hin hrk hL hZ hA6
  obtain ⟨e⟩ := hA6
  set ρ := (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion (hRP.trans hPM))
  set S := pCoreOf 2 H
  set C := Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  obtain ⟨-, T, hT, hTJ⟩ := h2.2.1
  have hJY : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L :=
    Subgroup.map_mono fun x hx => (Subgroup.mem_subgroupOf.mp hx).2
  have hcore := index_centralizer_le_three (U := ρ.range) e hJY hi hJne hT
    ((le_inf hT.1 Subgroup.le_normalizer).trans hTJ)
    ((P.isPGroup'.to_le hRP).of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective)
    (by
      rintro _ ⟨r, rfl⟩
      have hr3 : IsPGroup 3 (Subgroup.zpowers (r : G)) :=
        P.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hRP r.2))
      have hrL := h.mem_normalizer_of_threeASix hThree hcyc hzM hz3 hCz hin hrk hL hZ ⟨e⟩
        (hPM (hRP r.2)) hr3
      have hrS : (r : G) ∈ Subgroup.normalizer (S : Set G) :=
        localGroup_le_normalizer_pCoreOf 2 H (h.toD1Escape.le_H r.2)
      have hrN : (r : G) ∈
          Subgroup.normalizer ((Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) : Set G) := by
        have hrNS := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hrS)
        rw [Subgroup.mem_normalizer_iff] at hrL ⊢
        intro x
        simp only [Subgroup.mem_inf]
        exact and_congr (hrNS x) (hrL x)
      exact mem_normalizer_barM (hPM (hRP r.2)) hrN)
    (by
      rintro _ ⟨r, rfl⟩
      obtain ⟨l, hl, hlc⟩ := hdec (ρ r) ⟨⟨r, hPM (hRP r.2)⟩, hRP r.2, rfl⟩
      exact ⟨l, hl.2, hlc⟩)
  have hcomap : C.comap ρ = ((ρ.range ⊓ C).subgroupOf ρ.range).comap ρ.rangeRestrict := by
    ext r
    simp [Subgroup.mem_subgroupOf, MonoidHom.coe_rangeRestrict]
  rw [hcomap, Subgroup.index_comap_of_surjective _ ρ.rangeRestrict_surjective]
  exact hcore

end CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6

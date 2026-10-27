module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Tools
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma82
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace S8.L84

variable {G : Type} [Group G] [Finite G]

theorem step1 (h1016 : I1016ONAt G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hrk : 4 ≤ GLATwoLocalRank p G)
    {B L : Subgroup G} {x : G} (hB : GLAIsBmax p B) (hxB : x ∈ B) (hL : GLAPComponent p (cx x) L)
    (hBL : B ≤ (B ⊓ L) ⊔ Subgroup.zpowers x)
    (hT : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) = T ∧ ¬ T ≤ GLAPPrimeCoreOf p L)
    (hON : catalogIs (PSimple p L) (sporIs .ONan)) :
    p = 3 ∧ GLATwoLocalRank 3 G = 4 ∧ x ∉ L ∧ Nat.card (B ⊓ L : Subgroup G) = 3 ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hTL, hT2, hBT, -, hTO⟩ := hT
  have hFe : IsElemAbelian p (B ⊓ L) := CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB.1 inf_le_left
  have hFT : B ⊓ L ≤ Subgroup.normalizer (T : Set G) := inf_le_left.trans hBT
  have hxp : x ^ p = 1 := hB.1.2 x hxB
  have hzx : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact isElemAbelian_commute hB.1 hb.1 hxB
  have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hxN
  have hBle : Nat.card B ≤ Nat.card (B ⊓ L : Subgroup G) * p := by
    have h1 : Nat.card B ≤ Nat.card ((B ⊓ L) ⊔ Subgroup.zpowers x : Subgroup G) :=
      Subgroup.card_le_of_le hBL
    have h2 : 0 < Nat.card ((B ⊓ L) ⊓ Subgroup.zpowers x : Subgroup G) := Nat.card_pos
    calc Nat.card B ≤ Nat.card ((B ⊓ L) ⊔ Subgroup.zpowers x : Subgroup G) *
          Nat.card ((B ⊓ L) ⊓ Subgroup.zpowers x : Subgroup G) := h1.trans (Nat.le_mul_of_pos_right _ h2)
      _ = Nat.card (B ⊓ L : Subgroup G) * Nat.card (Subgroup.zpowers x) := hcard
      _ ≤ Nat.card (B ⊓ L : Subgroup G) * p := Nat.mul_le_mul_left _ hzx
  rcases h1016 p hp hp2 (cx x) L hL hON (B ⊓ L) T inf_le_right hFe hTL hT2 hTO hFT with
    ⟨hp3, hF27⟩ | hFp
  · subst hp3
    have hB81 : Nat.card B ≤ 3 ^ 4 := hBle.trans (by
      calc Nat.card (B ⊓ L : Subgroup G) * 3 ≤ 3 ^ 3 * 3 := Nat.mul_le_mul_right _ hF27
        _ = 3 ^ 4 := by norm_num)
    have hm4 : GLATwoLocalRank 3 G = 4 := by
      rw [hB.2.1] at hB81
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hB81
      omega
    have hBc : Nat.card B = 3 ^ 4 := by rw [hB.2.1, hm4]
    have hF : Nat.card (B ⊓ L : Subgroup G) = 3 ^ 3 := by
      rw [hBc] at hBle
      norm_num at hF27 hBle ⊢
      omega
    refine ⟨rfl, hm4, fun hxL => ?_, hF⟩
    have hBF : B ≤ B ⊓ L := hBL.trans (sup_le le_rfl ((Subgroup.zpowers_le).2 ⟨hxB, hxL⟩))
    have h1 : Nat.card B ≤ Nat.card (B ⊓ L : Subgroup G) := Subgroup.card_le_of_le hBF
    rw [hBc, hF] at h1
    norm_num at h1
  · exfalso
    have h1 : p ^ 4 ≤ p ^ GLATwoLocalRank p G := Nat.pow_le_pow_right hp.pos hrk
    have h2 : Nat.card B ≤ p * p := hBle.trans (Nat.mul_le_mul_right _ hFp)
    rw [hB.2.1] at h2
    have hp1 : 2 ≤ p := hp.two_le
    have h3 : p * p < p ^ 4 := by
      calc p * p = p ^ 2 := (pow_two p).symm
        _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

theorem center_trivial {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x : G} (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hL : GLAPComponent p (cx x) L) (hcyc : CycModSylow p L) (hxL : x ∉ L) :
    Nat.card (Subgroup.center (PQuot p L)) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hO : GLAPPrimeCore p (PQuot p L) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hpZ : p ∣ Nat.card (Subgroup.center (PQuot p L)) := by
    by_contra hnd
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center (PQuot p L))) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    have hbot : Subgroup.center (PQuot p L) = ⊥ :=
      (CFSG.pPrimeCore_eq_bot_iff (p := p) (G := PQuot p L)).1 hO _ inferInstance hcop
    exact hne (by rw [hbot]; exact Subgroup.card_bot)
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center (PQuot p L))) p hpZ
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (zc : PQuot p L)
  have hzc1 : (zc : PQuot p L) ≠ 1 := by
    intro h
    have : zc = 1 := Subtype.ext h
    rw [this, orderOf_one] at hzc
    exact hp.one_lt.ne hzc
  have hzcp : (zc : PQuot p L) ^ p = 1 := by
    have := pow_orderOf_eq_one zc
    rw [hzc] at this
    exact congrArg Subtype.val this
  have hlp : l ^ p ∈ GLAPPrimeCore p ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hl]
    exact hzcp
  set o : ↥L := l ^ p with ho
  have hmo : orderOf o ∣ Nat.card (GLAPPrimeCore p ↥L) := by
    have := orderOf_dvd_natCard (⟨o, hlp⟩ : ↥(GLAPPrimeCore p ↥L))
    rwa [Subgroup.orderOf_mk] at this
  have hcopm : Nat.Coprime (orderOf o) p :=
    (Nat.Coprime.coprime_dvd_left hmo (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥L)).symm)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopm hp.one_lt
  set z' : ↥L := l ^ (orderOf o * u) with hz'
  have hz'p : z' ^ p = 1 := by
    calc z' ^ p = l ^ (orderOf o * u * p) := by rw [hz', ← pow_mul]
      _ = (l ^ p) ^ (orderOf o * u) := by rw [← pow_mul]; congr 1; ring
      _ = o ^ (orderOf o * u) := by rw [ho]
      _ = (o ^ orderOf o) ^ u := by rw [pow_mul]
      _ = 1 := by rw [pow_orderOf_eq_one, one_pow]
  have hz'mk : (QuotientGroup.mk z' : PQuot p L) = zc := by
    rw [hz', QuotientGroup.mk_pow, hl, pow_eq_pow_mod _ hzcp, hu, pow_one]
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hzc1
    rw [← hz'mk, h]
    rfl
  set z : G := (z' : G) with hz
  have hzL : z ∈ L := z'.2
  have hz1 : z ≠ 1 := fun h => hz'1 (Subtype.ext h)
  have hz5 : z ^ p = 1 := by
    have := congrArg Subtype.val hz'p
    simpa using this
  have hzcm : CentMod p L z := by
    rw [centMod_iff]
    refine ⟨Subgroup.le_normalizer hzL, fun y hy => ?_⟩
    have hc := Subgroup.mem_center_iff.1 zc.2 (QuotientGroup.mk ⟨y, hy⟩)
    have h1 : (QuotientGroup.mk ⁅z', ⟨y, hy⟩⁆ : PQuot p L) = 1 := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      show _ * _ = _ * _
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hz'mk]
      exact hc.symm
    have h2 : ⁅z', ⟨y, hy⟩⁆ ∈ GLAPPrimeCore p ↥L := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : (⁅z, y⁆ : G) ∈ GLAPPrimeCoreOf p L := ⟨_, h2, rfl⟩
    have h4 := Subgroup.inv_mem _ h3
    rwa [commutatorElement_inv] at h4
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxcm : CentMod p L x :=
    centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hL.1 hl)))
  have hzx : z ∈ Subgroup.zpowers x := mem_zpowers_of_cyclic hp hcyc hxord hxcm (hL.1 hzL) hzcm hz5
  have hzord : orderOf z = p := orderOf_eq_prime hz5 hz1
  have hle : Subgroup.zpowers z ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hzx
  have hc1 : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
  have hc2 : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzord]
  have heq : Subgroup.zpowers z = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
  apply hxL
  have : x ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.2 hzL) this

theorem inf_zpowers_eq_bot {L : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxL : x ∉ L) :
    L ⊓ Subgroup.zpowers x = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ L.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd : Nat.card (L ⊓ Subgroup.zpowers x : Subgroup G) ∣ 3 := by
    rw [← hxo, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exfalso
    have heq : L ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hxo])
    have hxin : x ∈ L ⊓ Subgroup.zpowers x := by rw [heq]; exact Subgroup.mem_zpowers x
    exact hxL hxin.1

theorem E_facts {B L D₀ : Subgroup G} {x : G} (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hL : L ≤ cx x)
    (hD₀ : D₀ ≤ B ⊓ L) (hD₀c : Nat.card D₀ = 3 ^ 2) (hxL : x ∉ L) :
    D₀ ⊔ Subgroup.zpowers x ≤ B ∧ IsElemAbelian 3 (D₀ ⊔ Subgroup.zpowers x) ∧
      Nat.card (D₀ ⊔ Subgroup.zpowers x : Subgroup G) = 3 ^ 3 ∧
      L ⊓ Subgroup.centralizer ((D₀ ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
        L ⊓ Subgroup.centralizer (D₀ : Set G) ∧
      ∀ e ∈ D₀ ⊔ Subgroup.zpowers x, ∃ d ∈ D₀, ∃ i : ℕ, e = d * x ^ i := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ L.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hEB : D₀ ⊔ Subgroup.zpowers x ≤ B :=
    sup_le (fun d hd => (hD₀ hd).1) ((Subgroup.zpowers_le).2 hxB)
  have hD₀x : D₀ ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [S3.centralizer_zpowers x]
    exact fun d hd => hL (hD₀ hd).2
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (D₀ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.1 (hL (hD₀ hd).2)
  have hbot : D₀ ⊓ Subgroup.zpowers x = ⊥ := by
    have h := inf_zpowers_eq_bot hx3 hxL
    rw [eq_bot_iff] at h ⊢
    exact (inf_le_inf_right _ (fun d hd => (hD₀ hd).2)).trans h
  have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hxN
  rw [hbot, Subgroup.card_bot, mul_one, hD₀c, Nat.card_zpowers, hxo] at hcard
  refine ⟨hEB, CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB hEB, by rw [hcard]; norm_num, ?_, ?_⟩
  · rw [centralizer_sup_zpowers D₀ x, ← inf_assoc, inf_right_comm, inf_eq_left.2 hL]
  · intro e he
    obtain ⟨d, hd, b, hb, rfl⟩ := exists_mul_of_mem_sup hD₀x he
    obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hb)
    exact ⟨d, hd, i, rfl⟩

theorem I_comp_CE {x : G} {L D₀ E D I : Subgroup G} (hLn : cx x ≤ Subgroup.normalizer (L : Set G))
    (hxE : x ∈ E) (hDE : D ≤ E)
    (hLE : L ⊓ Subgroup.centralizer (E : Set G) = L ⊓ Subgroup.centralizer (D₀ : Set G))
    (hI : GLAPComponent 3 (L ⊓ Subgroup.centralizer (D₀ : Set G)) I) :
    GLAPComponent 3 (Subgroup.centralizer (E : Set G)) I ∧
      GLAPComponent 3 (Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (E : Set G)) I := by
  have hCEx : Subgroup.centralizer (E : Set G) ≤ cx x :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxE)
  have hCED : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.centralizer_le hDE
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer (E : Set G)) (Subgroup.centralizer (E : Set G)) := by
    refine IsSubnormal.step inf_le_right ?_ (IsSubnormal.refl _)
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 ?_
    intro g hg
    have hgL := hLn (hCEx hg)
    have hgC : g ∈ Subgroup.normalizer ((Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer hg
    rw [Subgroup.mem_normalizer_iff] at hgL hgC ⊢
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hgL h, hgC h]
  have h1 : GLAPComponent 3 (Subgroup.centralizer (E : Set G)) I := by
    rw [← hLE] at hI
    exact glaPComponent_of_isSubnormal' Nat.prime_three hsub hI
  refine ⟨h1, ?_⟩
  rw [inf_eq_right.2 hCED]
  exact h1

theorem diag_iso (h112 : I112At G) {X B E Y J₀ : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hX : CFSG.Open.IsKGroup ↥X) (hXY : X = Subgroup.centralizer (Y : Set G)) (hBX : B ≤ X)
    (hB : IsElemAbelian 3 B)
    (hrank : ∀ W U : Subgroup G, W ≤ X → IsElemAbelian 3 W → U ≤ X → U ≠ ⊥ → IsPGroup 2 U →
      W ≤ Subgroup.normalizer (U : Set G) → Nat.card W ≤ Nat.card B)
    (hEB : E ≤ B) (hYE : Y ≤ E) (hYidx : Nat.card Y * 3 = Nat.card E)
    (hJ₀ : GLAPComponent 3 (Subgroup.centralizer (E : Set G)) J₀)
    (h𝒞 : ∀ K ∈ 𝒞, GLAPComponent 3 X K)
    (hsup : (⨆ K ∈ 𝒞, K) = ⨆ g ∈ GLAPLayer 3 X, GLBConj g J₀)
    (htr : ∀ K ∈ 𝒞, ∀ K' ∈ 𝒞, ∃ e ∈ E, GLBConj e K = K')
    {K₁ K₂ : Subgroup G} (h1 : K₁ ∈ 𝒞) (h2 : K₂ ∈ 𝒞) (hne : K₁ ≠ K₂) :
    ¬ B ≤ Subgroup.normalizer (K₁ : Set G) ∧ Nonempty (PQuot 3 J₀ ≃* PSimple 3 K₁) := by
  obtain ⟨e, heE, he⟩ := htr K₁ h1 K₂ h2
  have heN : e ∉ Subgroup.normalizer (K₁ : Set G) := fun h =>
    hne (by rw [← he, mem_normalizer_iff_gLBConj_eq.1 h])
  have hnB : ¬ B ≤ Subgroup.normalizer (K₁ : Set G) := fun h => heN (h (hEB heE))
  refine ⟨hnB, (h112 X B K₁ hX hBX hB hrank (h𝒞 K₁ h1) hnB).2.2.2 e (hEB heE) heN J₀ ?_⟩
  have hK₁X : K₁ ≤ X := (h𝒞 K₁ h1).1
  have hYK : Y ≤ Subgroup.normalizer (K₁ : Set G) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkX : k ∈ X := hK₁X hk
    rw [hXY] at hkX
    exact (Subgroup.mem_centralizer_iff.1 hkX y hy).symm
  have heY : e ∉ Y := fun h => heN (hYK h)
  have hEeq : Y ⊔ Subgroup.zpowers e = E := by
    have hle : Y ⊔ Subgroup.zpowers e ≤ E := sup_le hYE ((Subgroup.zpowers_le).2 heE)
    have hlt : Nat.card Y < Nat.card (Y ⊔ Subgroup.zpowers e : Subgroup G) :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left
        (fun h => heY (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e))))
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : Y ≤ Y ⊔ Subgroup.zpowers e)
    have hdvd2 := Subgroup.card_dvd_of_le hle
    have hY0 : 0 < Nat.card Y := Nat.card_pos
    rw [← hYidx, hk] at hdvd2
    have hk3 : k ∣ 3 := (Nat.mul_dvd_mul_iff_left hY0).1 hdvd2
    have hk1 : 1 < k := by
      rw [hk] at hlt
      by_contra hk1
      push Not at hk1
      interval_cases k <;> simp at hlt
    have hk3' : k = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with h | h
      · omega
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [← hYidx, hk, hk3'])
  have hCE : Subgroup.centralizer (E : Set G) = X ⊓ cx e := by
    rw [← hEeq, centralizer_sup_zpowers, hXY]
  have hJ₀sup : J₀ ≤ ⨆ K ∈ 𝒞, K := by
    rw [hsup]
    calc J₀ = GLBConj 1 J₀ := (gLBConj_one J₀).symm
      _ ≤ ⨆ g ∈ GLAPLayer 3 X, GLBConj g J₀ :=
        le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 X) => GLBConj g J₀) 1 (GLAPLayer 3 X).one_mem
  have hsupcl : (⨆ K ∈ 𝒞, K) ≤ closureIn K₁ B := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨e', he', rfl⟩ := htr K₁ h1 K hK
    unfold closureIn GLBConj
    exact le_iSup₂ (f := fun (b : G) (_ : b ∈ B) => K₁.map (MulAut.conj b).toMonoidHom) e'⁻¹
      (B.inv_mem (hEB he'))
  have hclX : closureIn K₁ B ≤ X := by
    unfold closureIn
    refine iSup₂_le fun b hb => ?_
    rintro _ ⟨k, hk, rfl⟩
    show b * k * b⁻¹ ∈ X
    exact X.mul_mem (X.mul_mem (hBX hb) (hK₁X hk)) (X.inv_mem (hBX hb))
  have hJ₀M : J₀ ≤ closureIn K₁ B ⊓ cx e :=
    le_inf (hJ₀sup.trans hsupcl) (hJ₀.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 heE)))
  have hMCE : closureIn K₁ B ⊓ cx e ≤ Subgroup.centralizer (E : Set G) := by
    rw [hCE]
    exact inf_le_inf_right _ hclX
  exact glaPComponent_of_le Nat.prime_three hJ₀ hJ₀M hMCE

theorem three_A6_quot (ha6 : A6FactsAt G) {X D J₁ J₂ J₃ : Subgroup G}
    (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2) (hDX : D ≤ X)
    (hXD : X ≤ Subgroup.centralizer (D : Set G))
    (h1 : GLAPComponent 3 X J₁) (h2 : GLAPComponent 3 X J₂) (h3 : GLAPComponent 3 X J₃)
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃)
    (t1 : catalogIs (PSimple 3 J₁) isA6) (t2 : catalogIs (PSimple 3 J₂) isA6)
    (t3 : catalogIs (PSimple 3 J₃) isA6) :
    ∃ W T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), IsElemAbelian 3 W ∧ Nat.card W = 3 ^ 5 ∧
      T ≠ ⊥ ∧ IsPGroup 2 T ∧ W ≤ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
  have hne : ∀ {K₁ K₂ : Subgroup G}, GLAPComponent 3 X K₁ → GLAPComponent 3 X K₂ → K₁ ≠ K₂ →
      ⁅barX 3 X K₁, barX 3 X K₂⁆ = ⊥ := fun hK₁ hK₂ hKK =>
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK₁.2.2.1 hK₂.2.2.1
      (fun h => hKK (glaPComponent_unique hK₁ hK₂ h))
  obtain ⟨⟨y₁, hy₁, ho₁, hz₁, T, hTJ, hT1, hT2, hyT⟩, -⟩ := ha6 X J₁ h1 t1
  obtain ⟨⟨y₂, hy₂, ho₂, hz₂, -⟩, -⟩ := ha6 X J₂ h2 t2
  obtain ⟨⟨y₃, hy₃, ho₃, hz₃, -⟩, -⟩ := ha6 X J₃ h3 t3
  have hc12 := hne h1 h2 h12
  have hc13 := hne h1 h3 h13
  have hc23 := hne h2 h3 h23
  have hDZ : barX 3 X D ≤ Subgroup.center (↥X ⧸ GLAPPrimeCore 3 ↥X) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) z
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hgD := hXD g.2
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_centralizer_iff.1 hgD d (Subgroup.mem_subgroupOf.1 hd)).symm
  have hDe : IsElemAbelian 3 (barX 3 X D) := isElemAbelian_barX hD
  have hDc' : Nat.card (barX 3 X D) = 3 ^ 2 := by
    have hinj := injective_barX_comp Nat.prime_three (isPGroup_of_isElemAbelian hD) hDX
    have hrange : barX 3 X D =
        ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (D.subgroupOf X).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    rw [hrange, ← hDc, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv
  obtain ⟨hWe, hWc⟩ := card_three_comp_sup hc12 hc13 hc23 hy₁ hy₂ hy₃ ho₁ ho₂ ho₃ hz₁ hz₂ hz₃ hDe hDc' hDZ
  refine ⟨_, T, hWe, hWc, hT1, hT2, sup_le ?_ ?_⟩
  · rw [Subgroup.closure_le]
    have hcen : ∀ {K : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)} {y}, y ∈ K → ⁅barX 3 X J₁, K⁆ = ⊥ →
        y ∈ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      intro K y hy hK
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hK
      exact (Subgroup.mem_centralizer_iff.1 (hle (hTJ ht)) y hy).symm
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact hyT
    · exact hcen hy₂ hc12
    · exact hcen hy₃ hc13
  · intro d hd
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro t _
    exact (Subgroup.mem_center_iff.1 (hDZ hd) t)

theorem le_normalizer_of_le_centralizer {F E : Subgroup G} (h : F ≤ Subgroup.centralizer (E : Set G)) :
    E ≤ Subgroup.normalizer (F : Set G) := by
  intro e he
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact (Subgroup.mem_centralizer_iff.1 (h hf) e he).symm

theorem W_A6 (ha6 : A6FactsAt G) {X J E : Subgroup G} (hJ : GLAPComponent 3 X J)
    (hJt : IsTypeWithCenter 3 J isA6 1) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (hEJ : ∀ e ∈ E, CentMod 3 J e) :
    ∃ W : Subgroup G, W ≤ J ⊔ E ∧ IsElemAbelian 3 W ∧ Nat.card W = 3 ^ 5 := by
  have hcov : (J ⊓ Subgroup.centralizer (E : Set G)) ⊔ GLAPPrimeCoreOf 3 J = J :=
    S3.eq_inf_centralizer_sup_of_pgroup Nat.prime_three (isPGroup_of_isElemAbelian hE)
      (Subgroup.map_subtype_le _)
      (fun e he => normalizer_le_normalizer_glaPPrimeCoreOf 3 J (hEJ e he).1)
      (i183_coprime_card_glaPPrimeCoreOf Nat.prime_three J)
      (fun y hy e he => (hEJ e he).2 (Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers e)))
  obtain ⟨F, hFJ0, hFe, hFc⟩ := (ha6 X J hJ hJt.1).2 hJt.2 _ inf_le_left hcov
  have hFE : F ≤ Subgroup.centralizer (E : Set G) := hFJ0.trans inf_le_right
  have hbot : F ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro f ⟨hfF, hfE⟩
    exact Subgroup.mem_bot.2 (eq_one_of_mem_core Nat.prime_three
      (mem_core_of_centMod hJt.2 (hFJ0 hfF).1 (hEJ f hfE)) (hFe.2 f hfF))
  have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
    (le_normalizer_of_le_centralizer hFE)
  rw [hbot, Subgroup.card_bot, mul_one, hFc, hEc] at hcard
  exact ⟨F ⊔ E, sup_le_sup_right (hFJ0.trans inf_le_left) E, isElemAbelian_sup_of_commute hFe hE hFE,
    by rw [hcard]; norm_num⟩

theorem x_not_mem_D (hlb : LBalanceAt G 3) {x : G} {L D D₀ I J : Subgroup G} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hKx : CFSG.Open.IsKGroup ↥(cx x)) (hL : GLAPComponent 3 (cx x) L)
    (hLuniq : ∀ J' : Subgroup G, GLAPComponent 3 (cx x) J' → J' = L)
    (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2)
    (hDdec : ∀ e ∈ D, ∃ d ∈ D₀, ∃ i : ℕ, e = d * x ^ i)
    (hUa : ∀ d ∈ D₀, d ≠ 1 → UniqA6 (L ⊓ cx d)) (hIc : Nat.card (PQuot 3 I) = 360) (hIJ : I ≤ J)
    (hJ : GLAPComponent 3 (Subgroup.centralizer (D : Set G)) J)
    (hlt : ¬ J ≤ I ⊔ GLAPPrimeCoreOf 3 J) : x ∉ D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hxD
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨d', hd'D, hd'x⟩ : ∃ d' ∈ D, d' ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (h : D ≤ Subgroup.zpowers x)
    rw [Nat.card_zpowers, hxo, hDc] at h1
    norm_num at h1
  obtain ⟨d₀, hd₀, i, hd'⟩ := hDdec d' hd'D
  have hd₀1 : d₀ ≠ 1 := by
    rintro rfl
    rw [one_mul] at hd'
    exact hd'x (hd' ▸ Subgroup.npow_mem_zpowers x i)
  have hd₀D : d₀ ∈ D := by
    have h : d₀ = d' * (x ^ i)⁻¹ := by rw [hd']; group
    rw [h]
    exact D.mul_mem hd'D (D.inv_mem (D.pow_mem hxD i))
  have hd₀x : d₀ ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hD hd₀D hxD)
  have hCD : Subgroup.centralizer (D : Set G) = cx x ⊓ cx d₀ := by
    rw [centralizer_eq_inf hD hDc hxD hx1 hd'D hd'x, hd']
    exact inf_cx_mul_pow le_rfl d₀ i
  have hbal := hlb (cx x) (Subgroup.zpowers d₀) hKx ((Subgroup.zpowers_le).2 hd₀x)
    (isPGroup_zpowers_of_pow Nat.prime_three (hD.2 d₀ hd₀D))
  rw [S3.centralizer_zpowers d₀, glaPLayer_eq_of_uniq hL hLuniq, ← hCD] at hbal
  have hJL : J ≤ L := (le_sSup hJ : J ≤ GLAPLayer 3 (Subgroup.centralizer (D : Set G))).trans hbal
  have hJd₀ : J ≤ cx d₀ := hJ.1.trans (by rw [hCD]; exact inf_le_right)
  have hLd₀D : L ⊓ cx d₀ ≤ Subgroup.centralizer (D : Set G) := by
    rw [hCD]; exact inf_le_inf_right _ hL.1
  have hJ' : GLAPComponent 3 (L ⊓ cx d₀) J :=
    glaPComponent_of_le Nat.prime_three hJ (le_inf hJL hJd₀) hLd₀D
  obtain ⟨Ia, hIa, hIauniq, hIat, hIac⟩ := hUa d₀ hd₀ hd₀1
  have hJeq : J = Ia := hIauniq J hJ'
  exact hlt (cover_of_card Nat.prime_three hIJ (by rw [hJeq, hIac, hIc]))

theorem W_1430 (h106 : I106T1430At G) {X J D E : Subgroup G} (hJ : GLAPComponent 3 X J) (hT : T1430 J E)
    (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2) (hDE : D ≤ E) (hE : IsElemAbelian 3 E)
    (hJD : J ≤ Subgroup.centralizer (D : Set G)) (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    ∃ W : Subgroup G, W ≤ J ⊔ E ∧ IsElemAbelian 3 W ∧ Nat.card W = 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ha, hb⟩ := h106 X J hJ hT.1
  have hDcent : ∀ d ∈ D, CentMod 3 J d := fun d hd => centMod_of_comm fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hJD hj) d hd).symm
  have hFD : ∀ F : Subgroup G, F ≤ J → IsElemAbelian 3 F → (∀ f ∈ F, CentMod 3 J f → f = 1) →
      IsElemAbelian 3 (F ⊔ D) ∧ Nat.card (F ⊔ D : Subgroup G) = Nat.card F * 3 ^ 2 := by
    intro F hFJ hFe hFcm
    have hFD' : F ≤ Subgroup.centralizer (D : Set G) := hFJ.trans hJD
    have hbot : F ⊓ D = ⊥ := by
      rw [eq_bot_iff]
      rintro f ⟨hfF, hfD⟩
      exact Subgroup.mem_bot.2 (hFcm f hfF (hDcent f hfD))
    have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
      (le_normalizer_of_le_centralizer hFD')
    rw [hbot, Subgroup.card_bot, mul_one, hDc] at hcard
    exact ⟨isElemAbelian_sup_of_commute hFe hD hFD', hcard⟩
  by_cases hsp : catalogIs (PSimple 3 J) isSp48
  · obtain ⟨e, heE, hne⟩ := hT.2 hsp
    have he3 : e ^ 3 = 1 := hE.2 e heE
    obtain ⟨F, hFJe, hFe, hFc, hFcm⟩ := hb hsp e (hEJ heE) he3 hne
    obtain ⟨hMe, hMc⟩ := hFD F (hFJe.trans inf_le_left) hFe hFcm
    rw [hFc] at hMc
    set M : Subgroup G := F ⊔ D with hM
    have hMz : M ≤ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
      rw [S3.centralizer_zpowers e]
      refine sup_le (hFJe.trans inf_le_right) (fun d hd => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hE (hDE hd) heE)
    have heM : e ∉ M := by
      intro heM'
      apply hne
      have hFDc : F ≤ Subgroup.centralizer (D : Set G) := (hFJe.trans inf_le_left).trans hJD
      obtain ⟨f, hf, d, hd, rfl⟩ := exists_mul_of_mem_sup hFDc heM'
      have hfJ : f ∈ J := (hFJe hf).1
      exact S3.inducesInnerMod_mul ⟨f, hfJ, fun y _ => by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
        (S3.inducesInnerMod_of_centMod (hDcent d hd))
    have hbot : M ⊓ Subgroup.zpowers e = ⊥ := inf_zpowers_eq_bot he3 heM
    have heo : orderOf e = 3 := orderOf_eq_prime he3 (fun h => heM (h ▸ M.one_mem))
    have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
      (le_normalizer_of_le_centralizer hMz)
    rw [hbot, Subgroup.card_bot, mul_one, hMc, Nat.card_zpowers, heo] at hcard
    have hZe : IsElemAbelian 3 (Subgroup.zpowers e) :=
      CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hE ((Subgroup.zpowers_le).2 heE)
    refine ⟨M ⊔ Subgroup.zpowers e, ?_, isElemAbelian_sup_of_commute hMe hZe hMz,
      by rw [hcard]; norm_num⟩
    exact sup_le (sup_le ((hFJe.trans inf_le_left).trans le_sup_left) (hDE.trans le_sup_right))
      (((Subgroup.zpowers_le).2 heE).trans le_sup_right)
  · obtain ⟨F, hFJ, hFe, hFc, hFcm⟩ := ha hsp
    obtain ⟨hWe, hWc⟩ := hFD F hFJ hFe hFcm
    rw [hFc] at hWc
    exact ⟨F ⊔ D, sup_le_sup hFJ hDE, hWe, by rw [hWc]; norm_num⟩

theorem Ka_comp (hlb : LBalanceAt G 3) {x a d₀ : G} {L K D₀ I : Subgroup G}
    (hKx : CFSG.Open.IsKGroup ↥(cx x)) (hL : GLAPComponent 3 (cx x) L)
    (hLuniq : ∀ J' : Subgroup G, GLAPComponent 3 (cx x) J' → J' = L)
    (hD₀x : D₀ ≤ cx x) (hD₀ : IsPGroup 3 D₀) (ha3 : a ^ 3 = 1) (hax : a ∈ cx x)
    (hLa : L ⊓ cx a = L ⊓ cx d₀) (hUa : UniqA6 (L ⊓ cx d₀))
    (hK : GLAPComponent 3 (cx a) K) (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hD₀K : D₀ ≤ Subgroup.normalizer (K : Set G))
    (hI : GLAPComponent 3 ((K ⊓ cx x) ⊓ Subgroup.centralizer (D₀ : Set G)) I) :
    ∃ Ia : Subgroup G, GLAPComponent 3 (K ⊓ cx x) Ia ∧ IsTypeWithCenter 3 Ia isA6 1 := by
  have hKxK : CFSG.Open.IsKGroup ↥((K ⊓ cx x) ⊔ D₀) :=
    CFSG.Open.IsKGroup.of_le hKx (sup_le inf_le_right hD₀x)
  have hPN : D₀ ≤ Subgroup.normalizer ((K ⊓ cx x : Subgroup G) : Set G) := fun d hd =>
    mem_normalizer_inf (hD₀K hd) (Subgroup.le_normalizer (hD₀x hd))
  obtain ⟨Q, hQ⟩ := exists_comp_of_sub hlb hKxK hD₀ hPN hI
  have hsub : IsSubnormal (K ⊓ cx x) (cx a ⊓ cx x) := isSubnormal_inf hK.2.1 (cx x)
  have hQY : GLAPComponent 3 (cx a ⊓ cx x) Q := glaPComponent_of_isSubnormal' Nat.prime_three hsub hQ
  have hbal := hlb (cx x) (Subgroup.zpowers a) hKx ((Subgroup.zpowers_le).2 hax)
    (isPGroup_zpowers_of_pow Nat.prime_three ha3)
  rw [S3.centralizer_zpowers a, glaPLayer_eq_of_uniq hL hLuniq, inf_comm] at hbal
  have hQL : Q ≤ L := (le_sSup hQY : Q ≤ GLAPLayer 3 (cx a ⊓ cx x)).trans hbal
  have hQa : Q ≤ cx a := hQY.1.trans inf_le_left
  have hLaY : L ⊓ cx a ≤ cx a ⊓ cx x := fun g hg => ⟨hg.2, hL.1 hg.1⟩
  have hQ' : GLAPComponent 3 (L ⊓ cx a) Q := glaPComponent_of_le Nat.prime_three hQY (le_inf hQL hQa) hLaY
  rw [hLa] at hQ'
  obtain ⟨Ia, -, hIauniq, hIat, -⟩ := hUa
  exact ⟨Q, hQ, (hIauniq Q hQ') ▸ hIat⟩

theorem A_facts {B L H : Subgroup G} {x : G} (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hLx : L ≤ cx x)
    (hxL : x ∉ L) (hBL : B ≤ (B ⊓ L) ⊔ Subgroup.zpowers x) (hHL : H ≤ L) (hH : IsElemAbelian 3 H)
    (hHc : Nat.card H = 3 ^ 4) (hFH : B ⊓ L ≤ H) :
    IsElemAbelian 3 (H ⊔ Subgroup.zpowers x) ∧
      Nat.card (H ⊔ Subgroup.zpowers x : Subgroup G) = 3 ^ 5 ∧ B ≤ H ⊔ Subgroup.zpowers x ∧
      H ⊔ Subgroup.zpowers x ≤ cx x ∧ (H ⊔ Subgroup.zpowers x) ⊓ L = H ∧ x ∉ H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ L.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hHx : H ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [S3.centralizer_zpowers x]
    exact hHL.trans hLx
  have hZ : IsElemAbelian 3 (Subgroup.zpowers x) :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB ((Subgroup.zpowers_le).2 hxB)
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLx (hHL hh))
  have hLZ := inf_zpowers_eq_bot hx3 hxL
  have hbot : H ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff] at hLZ ⊢
    exact (inf_le_inf_right _ hHL).trans hLZ
  have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hxN
  rw [hbot, Subgroup.card_bot, mul_one, hHc, Nat.card_zpowers, hxo] at hcard
  have hxx : x ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 rfl
  refine ⟨isElemAbelian_sup_of_commute hH hZ hHx, by rw [hcard]; norm_num,
    hBL.trans (sup_le_sup_right hFH _), sup_le (hHL.trans hLx) ((Subgroup.zpowers_le).2 hxx), ?_,
    fun h => hxL (hHL h)⟩
  apply le_antisymm
  · rintro y ⟨hyA, hyL⟩
    obtain ⟨h, hh, b, hb, rfl⟩ := exists_mul_of_mem_sup hHx hyA
    have hbL : b ∈ L := by
      have := L.mul_mem (L.inv_mem (hHL hh)) hyL
      simpa using this
    have hb1 : b = 1 := by
      have : b ∈ L ⊓ Subgroup.zpowers x := ⟨hbL, hb⟩
      rw [hLZ] at this
      exact this
    rw [hb1, mul_one]
    exact hh
  · exact le_inf le_sup_left hHL

theorem a_not_conj (hk : KFactsAt G) {x a : G} {L K : Subgroup G}
    (hLuniq : ∀ J' : Subgroup G, GLAPComponent 3 (cx x) J' → J' = L)
    (hON : catalogIs (PSimple 3 L) (sporIs .ONan)) (hK : GLAPComponent 3 (cx a) K) (hKt : SpA12Type K) :
    ∀ g : G, g * x * g⁻¹ ≠ a ∧ g * x⁻¹ * g⁻¹ ≠ a := by
  have hk5 := (hk (cx a) K hK hKt).1
  have key : ∀ g : G, cx a = GLBConj g⁻¹ (cx x) → False := by
    intro g h
    have h1 := glaPComponent_gLBConj hK g
    rw [h, gLBConj_gLBConj_inv] at h1
    have h2 := hLuniq _ h1
    apply hk5
    have h3 : catalogIs (PSimple 3 (GLBConj g K)) (sporIs .ONan) := h2 ▸ hON
    obtain ⟨e⟩ := pQuot_conj 3 g K
    obtain ⟨f⟩ := nonempty_pSimple_congr e
    exact (catalogIs_congr f).1 h3
  have hcinv : cx x⁻¹ = cx x := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  intro g
  constructor
  · intro h
    apply key g
    rw [← h]
    have := centralizer_singleton_gLBConj g⁻¹ x
    rw [inv_inv] at this
    exact this
  · intro h
    apply key g
    rw [← h]
    have := centralizer_singleton_gLBConj g⁻¹ x⁻¹
    rw [inv_inv] at this
    rw [show cx (g * x⁻¹ * g⁻¹) = Subgroup.centralizer ({g * x⁻¹ * g⁻¹} : Set G) from rfl, this]
    exact congrArg (GLBConj g⁻¹) hcinv

theorem centMod_mem_normalizer_sup_core {p : ℕ} {K T : Subgroup G} (hTK : T ≤ K) {q : G}
    (hq : CentMod p K q) :
    q ∈ Subgroup.normalizer ((T ⊔ GLAPPrimeCoreOf p K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  have hO := mem_normalizer_iff_gLBConj_eq.1 (normalizer_le_normalizer_glaPPrimeCoreOf p K hq.1)
  have hle : GLBConj q (T ⊔ GLAPPrimeCoreOf p K) ≤ T ⊔ GLAPPrimeCoreOf p K := by
    unfold GLBConj at hO ⊢
    rw [Subgroup.map_sup, hO]
    refine sup_le ?_ le_sup_right
    rintro _ ⟨t, ht, rfl⟩
    have hc : ⁅t, q⁻¹⁆ ∈ GLAPPrimeCoreOf p K :=
      hq.2 (Subgroup.commutator_mem_commutator (hTK ht) (Subgroup.inv_mem _ (Subgroup.mem_zpowers q)))
    have heq : (MulAut.conj q⁻¹).toMonoidHom t = ⁅t, q⁻¹⁆⁻¹ * t := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hc)) (Subgroup.mem_sup_left ht)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  unfold GLBConj
  rw [Subgroup.card_map_of_injective (MulAut.conj q⁻¹).injective]

theorem cen_rank_le (hk : KFactsAt G) {X K : Subgroup G} (hK : GLAPComponent 3 X K) (hKt : SpA12Type K)
    (hrk : GLATwoLocalRank 3 G ≤ 4) :
    ∀ Q : Subgroup G, IsElemAbelian 3 Q → (∀ q ∈ Q, CentMod 3 K q) → Nat.card Q ≤ 3 := by
  intro Q hQ hQc
  by_contra hlt
  push Not at hlt
  obtain ⟨-, -, hk2, -, -⟩ := hk X K hK hKt
  have hcov : (K ⊓ Subgroup.centralizer (Q : Set G)) ⊔ GLAPPrimeCoreOf 3 K = K :=
    S3.eq_inf_centralizer_sup_of_pgroup Nat.prime_three (isPGroup_of_isElemAbelian hQ)
      (Subgroup.map_subtype_le _)
      (fun q hq => normalizer_le_normalizer_glaPPrimeCoreOf 3 K (hQc q hq).1)
      (i183_coprime_card_glaPPrimeCoreOf Nat.prime_three K)
      (fun y hy q hq => (hQc q hq).2 (Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers q)))
  obtain ⟨F, T, hFK0, hFe, hFc, hTK, hT2, hTO, hFT⟩ := hk2 _ inf_le_left hcov
  have hFQ : F ≤ Subgroup.centralizer (Q : Set G) := hFK0.trans inf_le_right
  have hbot : F ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro f ⟨hfF, hfQ⟩
    exact Subgroup.mem_bot.2 (eq_one_of_mem_core Nat.prime_three
      (mem_core_of_centMod hKt.2 (hFK0 hfF).1 (hQc f hfQ)) (hFe.2 f hfF))
  have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
    (le_normalizer_of_le_centralizer hFQ)
  rw [hbot, Subgroup.card_bot, mul_one, hFc] at hcard
  obtain ⟨k, hkQ⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hQ
  have hk2' : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> simp_all
  have hQ9 : 9 ≤ Nat.card Q := by
    rw [hkQ]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2'
  have hT1 : T ≠ ⊥ := fun h => hTO (h ▸ bot_le)
  have hWN : F ⊔ Q ≤ Subgroup.normalizer ((T ⊔ GLAPPrimeCoreOf 3 K : Subgroup G) : Set G) := by
    refine sup_le (fun f hf => ?_) (fun q hq => centMod_mem_normalizer_sup_core hTK (hQc q hq))
    exact mem_normalizer_sup (hFT hf) (le_normalizer_glaPPrimeCoreOf 3 K (hFK0 hf).1)
  have h1 := pump_contra Nat.prime_three (by norm_num) hTK hT2 hT1
    (isElemAbelian_sup_of_commute hFe hQ hFQ) hWN
  rw [hcard] at h1
  have h2 : 3 ^ GLATwoLocalRank 3 G ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hrk
  have h3 : 3 ^ 3 * 9 ≤ 3 ^ 3 * Nat.card Q := Nat.mul_le_mul_left _ hQ9
  omega

theorem exists_centMod_mul_of_inducesInnerMod {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) (h : InducesInnerMod p J g) :
    ∃ c ∈ centModSubgroup p J, ∃ l ∈ J, g = c * l := by
  obtain ⟨l, hl, hy⟩ := h
  refine ⟨g * l⁻¹, ⟨?_, fun x hx => ?_⟩, l, hl, by group⟩
  · exact Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (Subgroup.le_normalizer hl))
  · have h1 := hy x⁻¹ (J.inv_mem hx)
    have h2 : g * ((l⁻¹ * x⁻¹ * l)⁻¹ * (g⁻¹ * x⁻¹ * g)) * g⁻¹ ∈ GLAPPrimeCoreOf p J :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p J hg) _).1 h1
    have h3 : ⁅x, g * l⁻¹⁆ = (g * ((l⁻¹ * x⁻¹ * l)⁻¹ * (g⁻¹ * x⁻¹ * g)) * g⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h3]; exact Subgroup.inv_mem _ h2

open scoped Pointwise in
theorem sup_pow_comm_mem {p : ℕ} {A K : Subgroup G} (hA : IsElemAbelian p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    (∀ q ∈ A ⊔ K, q ^ p ∈ K) ∧ ∀ q ∈ A ⊔ K, ∀ q' ∈ A ⊔ K, ⁅q, q'⁆ ∈ K := by
  have hKN : K ≤ A ⊔ K := le_sup_right
  have hNn : A ⊔ K ≤ Subgroup.normalizer (K : Set G) := sup_le hAK Subgroup.le_normalizer
  haveI hKnorm : (K.subgroupOf (A ⊔ K)).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).2 hNn
  have hrep : ∀ q ∈ A ⊔ K, ∃ a ∈ A, ∃ k ∈ K, q = a * k := by
    intro q hq
    have hq' : q ∈ ((A : Set G) * (K : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A K hAK]
      exact hq
    obtain ⟨a, ha, k, hk, hqk⟩ := Set.mem_mul.1 hq'
    exact ⟨a, ha, k, hk, hqk.symm⟩
  let φ : ↥(A ⊔ K) →* ↥(A ⊔ K) ⧸ K.subgroupOf (A ⊔ K) := QuotientGroup.mk' (K.subgroupOf (A ⊔ K))
  have hker : ∀ n : ↥(A ⊔ K), φ n = 1 ↔ (n : G) ∈ K := fun n => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hφA : ∀ q : ↥(A ⊔ K), ∃ a : G, ∃ ha : a ∈ A, φ q = φ ⟨a, Subgroup.mem_sup_left ha⟩ := by
    intro q
    obtain ⟨a, ha, k, hk, hq⟩ := hrep q.1 q.2
    refine ⟨a, ha, ?_⟩
    have : q = ⟨a, Subgroup.mem_sup_left ha⟩ * ⟨k, Subgroup.mem_sup_right hk⟩ := Subtype.ext hq
    rw [this, map_mul, (hker ⟨k, Subgroup.mem_sup_right hk⟩).2 hk, mul_one]
  constructor
  · intro q hq
    obtain ⟨a, ha, hqa⟩ := hφA ⟨q, hq⟩
    have h1 : φ ((⟨q, hq⟩ : ↥(A ⊔ K)) ^ p) = 1 := by
      rw [map_pow, hqa, ← map_pow]
      have : (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(A ⊔ K)) ^ p = 1 := Subtype.ext (by simpa using hA.2 a ha)
      rw [this, map_one]
    exact (hker _).1 h1
  · intro q hq q' hq'
    obtain ⟨a, ha, hqa⟩ := hφA ⟨q, hq⟩
    obtain ⟨a', ha', hqa'⟩ := hφA ⟨q', hq'⟩
    have h1 : φ ⁅(⟨q, hq⟩ : ↥(A ⊔ K)), ⟨q', hq'⟩⁆ = 1 := by
      rw [map_commutatorElement, hqa, hqa', ← map_commutatorElement]
      have : ⁅(⟨a, Subgroup.mem_sup_left ha⟩ : ↥(A ⊔ K)), (⟨a', Subgroup.mem_sup_left ha'⟩ : ↥(A ⊔ K))⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subtype.ext (isElemAbelian_commute hA ha ha')
      rw [this, map_one]
    exact (hker _).1 h1


theorem A_index_le (hk : KFactsAt G) {X K A : Subgroup G} (hK : GLAPComponent 3 X K) (hKt : SpA12Type K)
    (hA : IsElemAbelian 3 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hcen : ∀ Q : Subgroup G, IsElemAbelian 3 Q → (∀ q ∈ Q, CentMod 3 K q) → Nat.card Q ≤ 3) :
    Nat.card A ≤ 3 * Nat.card (A ⊓ K : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKN : K ≤ A ⊔ K := le_sup_right
  have hAN : A ≤ A ⊔ K := le_sup_left
  have hNn : A ⊔ K ≤ Subgroup.normalizer (K : Set G) := sup_le hAK Subgroup.le_normalizer
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G, Y = centModSubgroup 3 K ⊓ (A ⊔ K) := ⟨_, rfl⟩
  have hYZ : Y ≤ centModSubgroup 3 K := by rw [hYdef]; exact inf_le_left
  have hYN : Y ≤ A ⊔ K := by rw [hYdef]; exact inf_le_right
  have hYn : Y ≤ Subgroup.normalizer (K : Set G) := hYN.trans hNn
  have hdec : ∀ a ∈ A, ∃ c ∈ Y, ∃ l ∈ K, a = c * l := by
    intro a ha
    have hinn := (hk X K hK hKt).2.2.2.1 a (hAK ha) ⟨1, by simpa using hA.2 a ha⟩
    obtain ⟨c, hc, l, hl, hal⟩ := exists_centMod_mul_of_inducesInnerMod (hAK ha) hinn
    refine ⟨c, ?_, l, hl, hal⟩
    rw [hYdef]
    refine ⟨hc, ?_⟩
    have hcl : c * l ∈ A := hal ▸ ha
    have h1 : c * l * l⁻¹ ∈ A ⊔ K := Subgroup.mul_mem _ (hAN hcl) (Subgroup.inv_mem _ (hKN hl))
    simpa using h1
  have hNY : A ⊔ K = Y ⊔ K := by
    apply le_antisymm
    · refine sup_le (fun a ha => ?_) le_sup_right
      obtain ⟨c, hc, l, hl, rfl⟩ := hdec a ha
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hl)
    · exact sup_le hYN hKN
  have hYK : Y ⊓ K ≤ GLAPPrimeCoreOf 3 K := fun y hy =>
    mem_core_of_centMod hKt.2 hy.2 (centMod_iff.2 (hYZ hy.1))
  have hf1 := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := Y) hYn
  have hf2 := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := A) hAK
  rw [sup_comm K Y, ← hNY, inf_comm K Y] at hf1
  rw [sup_comm K A, inf_comm K A] at hf2
  have hk0 : 0 < Nat.card K := Nat.card_pos
  have key : Nat.card A * Nat.card (Y ⊓ K : Subgroup G) = Nat.card (A ⊓ K : Subgroup G) * Nat.card Y := by
    apply Nat.eq_of_mul_eq_mul_left hk0
    calc Nat.card K * (Nat.card A * Nat.card (Y ⊓ K : Subgroup G))
        = (Nat.card K * Nat.card A) * Nat.card (Y ⊓ K : Subgroup G) := by ring
      _ = (Nat.card (A ⊔ K : Subgroup G) * Nat.card (A ⊓ K : Subgroup G)) *
            Nat.card (Y ⊓ K : Subgroup G) := by rw [hf2]
      _ = (Nat.card (A ⊔ K : Subgroup G) * Nat.card (Y ⊓ K : Subgroup G)) *
            Nat.card (A ⊓ K : Subgroup G) := by ring
      _ = (Nat.card K * Nat.card Y) * Nat.card (A ⊓ K : Subgroup G) := by rw [hf1]
      _ = Nat.card K * (Nat.card (A ⊓ K : Subgroup G) * Nat.card Y) := by ring
  obtain ⟨a, haA⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hA
  obtain ⟨b, hbA⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three
    (isElemAbelian_mono hA (inf_le_left : A ⊓ K ≤ A))
  have hba : b ≤ a := by
    have h1 : Nat.card (A ⊓ K : Subgroup G) ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
    rw [haA, hbA] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hba
  have hY : Nat.card Y = 3 ^ n * Nat.card (Y ⊓ K : Subgroup G) := by
    rw [haA, hbA, pow_add] at key
    have h3b : 0 < 3 ^ b := by positivity
    apply Nat.eq_of_mul_eq_mul_left h3b
    calc 3 ^ b * Nat.card Y = 3 ^ b * 3 ^ n * Nat.card (Y ⊓ K : Subgroup G) := key.symm
      _ = 3 ^ b * (3 ^ n * Nat.card (Y ⊓ K : Subgroup G)) := by ring
  obtain ⟨Q', hQ'⟩ := Sylow.exists_subgroup_card_pow_prime (G := Y) 3 (n := n)
    (by rw [hY]; exact dvd_mul_right _ _)
  have hQY : Q'.map Y.subtype ≤ Y := Subgroup.map_subtype_le Q'
  have hQc : Nat.card (Q'.map Y.subtype) = 3 ^ n := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hQ']
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup G, Q = Q'.map Y.subtype := ⟨_, rfl⟩
  rw [← hQdef] at hQY hQc
  have hcop : Nat.Coprime (3 ^ n) (Nat.card (GLAPPrimeCoreOf 3 K)) :=
    Nat.Coprime.pow_left n (i183_coprime_card_glaPPrimeCoreOf Nat.prime_three K)
  have hQK : ∀ z ∈ Q, z ∈ K → z = 1 := by
    intro z hzQ hzK
    have hzO : z ∈ GLAPPrimeCoreOf 3 K := hYK ⟨hQY hzQ, hzK⟩
    have h1 : orderOf z ∣ 3 ^ n := by
      have := Subgroup.orderOf_dvd_natCard Q hzQ
      rwa [hQc] at this
    have h2 : orderOf z ∣ Nat.card (GLAPPrimeCoreOf 3 K) := Subgroup.orderOf_dvd_natCard _ hzO
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  obtain ⟨hcube, hcomm⟩ := sup_pow_comm_mem hA hAK
  have hQe : IsElemAbelian 3 Q := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have h1 : ⁅x.1, y.1⁆ = 1 := by
        apply hQK
        · rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ x.2 y.2) (Subgroup.inv_mem _ x.2))
            (Subgroup.inv_mem _ y.2)
        · exact hcomm _ (hYN (hQY x.2)) _ (hYN (hQY y.2))
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    · exact hQK _ (Q.pow_mem hx 3) (hcube x (hYN (hQY hx)))
  have hQ3 : 3 ^ n ≤ 3 := by
    have := hcen Q hQe (fun q hq => centMod_iff.2 (hYZ (hQY hq)))
    rwa [hQc] at this
  calc Nat.card A = 3 ^ b * 3 ^ n := by rw [haA, pow_add]
    _ ≤ 3 ^ b * 3 := Nat.mul_le_mul_left _ hQ3
    _ = 3 * Nat.card (A ⊓ K : Subgroup G) := by rw [hbA, mul_comm]

theorem A_split (hk : KFactsAt G) {X K A : Subgroup G} {a : G} (hK : GLAPComponent 3 X K)
    (hKt : SpA12Type K) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 5) (haA : a ∈ A)
    (ha1 : a ≠ 1) (haK : CentMod 3 K a) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hcen : ∀ Q : Subgroup G, IsElemAbelian 3 Q → (∀ q ∈ Q, CentMod 3 K q) → Nat.card Q ≤ 3) :
    Nat.card (A ⊓ K : Subgroup G) = 3 ^ 4 ∧ A ≤ (A ⊓ K) ⊔ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx := A_index_le hk hK hKt hA hAK hcen
  have hAK4 : Nat.card (A ⊓ K : Subgroup G) ≤ 3 ^ 4 :=
    (hk X K hK hKt).2.1 _ inf_le_right (CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hA inf_le_left)
  have hcard : Nat.card (A ⊓ K : Subgroup G) = 3 ^ 4 := by
    rw [hAc] at hidx
    norm_num at hidx hAK4 ⊢
    omega
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have haK' : a ∉ K := fun h =>
    ha1 (eq_one_of_mem_core Nat.prime_three (mem_core_of_centMod hKt.2 h haK) ha3)
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_inf ?_ haK.1
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact isElemAbelian_commute hA hb haA
  have hbot : (A ⊓ K) ⊓ Subgroup.zpowers a = ⊥ := by
    have h := inf_zpowers_eq_bot ha3 haK'
    rw [eq_bot_iff] at h ⊢
    exact (inf_le_inf_right _ inf_le_right).trans h
  have hprod := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer haN
  rw [hbot, Subgroup.card_bot, mul_one, hcard, Nat.card_zpowers, hao] at hprod
  have hle : (A ⊓ K) ⊔ Subgroup.zpowers a ≤ A := sup_le inf_le_left ((Subgroup.zpowers_le).2 haA)
  have heq : (A ⊓ K) ⊔ Subgroup.zpowers a = A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hAc, hprod]; norm_num)
  exact ⟨hcard, heq.ge⟩

theorem NA_le_NK {K A : Subgroup G} {a : G} (hK : GLAPComponent 3 (cx a) K)
    (hKZ : Nat.card (Subgroup.center (PQuot 3 K)) = 1) (hA : IsElemAbelian 3 A)
    (hAc : Nat.card A = 3 ^ 5) (hAK : Nat.card (A ⊓ K : Subgroup G) = 3 ^ 4) :
    Subgroup.normalizer (A : Set G) ⊓ cx a ≤ Subgroup.normalizer (K : Set G) := by
  rintro n ⟨hnA, hna⟩
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  have hKn : GLAPComponent 3 (cx a) (GLBConj n K) := by
    have h1 := glaPComponent_gLBConj hK n
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hna)] at h1
  have hint := CFSG.HardMathSupport.Solomon.LocalBalance.inf_le_oPrimePOf_of_ne Nat.prime_three hK hKn
    (Ne.symm hne)
  have hcore := oPrimePOf_le_core Nat.prime_three hK hKZ
  have hAn : GLBConj n A = A := mem_normalizer_iff_gLBConj_eq.1 hnA
  have hbot : (A ⊓ K) ⊓ GLBConj n (A ⊓ K) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨hyA, hyK⟩, hyn⟩
    rw [gLBConj_inf] at hyn
    have hyO := hcore (hint ⟨hyK, hyn.2⟩)
    exact Subgroup.mem_bot.2 (eq_one_of_mem_core Nat.prime_three hyO (hA.2 y hyA))
  have hcn : Nat.card (GLBConj n (A ⊓ K) : Subgroup G) = 3 ^ 4 := by
    unfold GLBConj
    rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hAK]
  have hle : GLBConj n (A ⊓ K) ≤ A := by
    rw [gLBConj_inf, hAn]
    exact inf_le_left
  have hN : GLBConj n (A ⊓ K) ≤ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := by
    refine le_normalizer_of_le_centralizer fun f hf => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact isElemAbelian_commute hA (hle he) hf.1
  have hprod := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hbot, Subgroup.card_bot, mul_one, hAK, hcn] at hprod
  have h1 := Subgroup.card_le_of_le (sup_le inf_le_left hle : (A ⊓ K) ⊔ GLBConj n (A ⊓ K) ≤ A)
  rw [hprod, hAc] at h1
  norm_num at h1

end S8.L84

end CFSG.LocalAnalysis.GLTheoremA

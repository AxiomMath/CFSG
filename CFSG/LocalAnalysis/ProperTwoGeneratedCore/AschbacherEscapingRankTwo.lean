module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCentralizerStructure
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

@[expose] def HighRankEscapingStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
      Subgroup.centralizer ({z} : Set G) ≤ H →
      ∀ u : G, orderOf u = 2 → u ∈ (S : Subgroup G) →
        (∀ P : Subgroup G, P ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 P →
          Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) :
            Subgroup G)) →
        3 ≤ CFSG.Open.pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G)) →
        ¬ Subgroup.centralizer ({u} : Set G) ≤ H →
        u ∉ localInvolutionPointHull z u

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_le_of_conj {H : Subgroup G} {a b h : G} (hh : h ∈ H)
    (hab : h⁻¹ * b * h = a) (hb : Subgroup.centralizer ({b} : Set G) ≤ H) :
    Subgroup.centralizer ({a} : Set G) ≤ H := by
  intro x hx
  subst hab
  have hx' : h * x * h⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc h * x * h⁻¹ * b = h * (x * (h⁻¹ * b * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * b * h) * x) * h⁻¹ := by rw [hx]
      _ = b * (h * x * h⁻¹) := by group
  have := H.mul_mem (H.mul_mem (H.inv_mem hh) (hb hx')) hh
  simpa [mul_assoc] using this

theorem exists_conj_mem_sylow {p : ℕ} [Fact p.Prime] (S : Sylow p G) {P : Subgroup G}
    (hP : IsPGroup p P) : ∃ g : G, ∀ x ∈ P, g⁻¹ * x * g ∈ (S : Subgroup G) := by
  obtain ⟨S', hPS'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  refine ⟨g⁻¹, fun x hx => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, inv_inv]
  exact Set.mem_smul_set.mpr ⟨x, hPS' hx, rfl⟩

theorem card_le_card_sylow_of_le {p : ℕ} [Fact p.Prime] {M P : Subgroup G} (Q : Sylow p M)
    (hPM : P ≤ M) (hP : IsPGroup p P) : Nat.card P ≤ Nat.card Q := by
  obtain ⟨Q', hPQ'⟩ := (hP.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  have h1 : Nat.card (P.subgroupOf M) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
  have h2 : Nat.card Q' = Nat.card Q := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  rw [← h1, ← h2]
  exact Subgroup.card_le_of_le hPQ'

theorem exists_sylow_eq_subgroupOf {p : ℕ} {M T : Subgroup G} (hTM : T ≤ M)
    (hT : IsPGroup p T)
    (hmax : ∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → Nat.card Q ≤ Nat.card T) :
    ∃ Q : Sylow p M, (Q : Subgroup M) = T.subgroupOf M := by
  obtain ⟨Q, hTQ⟩ := (hT.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hTQ ?_).symm⟩
  change Nat.card Q ≤ Nat.card (T.subgroupOf M)
  have h1 : Nat.card ((Q : Subgroup M).map M.subtype) = Nat.card Q :=
    Subgroup.card_map_of_injective M.subtype_injective
  have h2 : Nat.card (T.subgroupOf M) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv
  have h3 := hmax _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map M.subtype)
  omega

theorem exists_conj_mem_of_card_le {p : ℕ} [Fact p.Prime] {M T P : Subgroup G} (hTM : T ≤ M)
    (hT : IsPGroup p T)
    (hmax : ∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → Nat.card Q ≤ Nat.card T)
    (hPM : P ≤ M) (hP : IsPGroup p P) :
    ∃ c ∈ M, ∀ x ∈ P, c⁻¹ * x * c ∈ T := by
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_subgroupOf hTM hT hmax
  obtain ⟨c, hc⟩ :=
    exists_conj_mem_sylow Q (hP.comap_of_injective M.subtype M.subtype_injective)
  refine ⟨c, c.property, fun x hx => ?_⟩
  have := hc ⟨x, hPM hx⟩ hx
  rw [hQ] at this
  exact this

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

omit [Finite G] in
theorem zpowers_le_centralizer_zpowers {a b : G} (h : Commute a b) :
    Subgroup.zpowers a ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (h.symm.zpow_left k).eq

omit [Finite G] in
theorem not_odd_card_of_orderOf_eq_two {K : Subgroup G} {x : G} (hx : x ∈ K)
    (h : orderOf x = 2) : ¬ Odd (Nat.card K) := by
  intro hodd
  have hdvd : orderOf (⟨x, hx⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, h] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem three_le_pRank_of_commuting_involutions {K : Subgroup G} {a b t : G}
    (haK : a ∈ K) (hbK : b ∈ K) (htK : t ∈ K)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (ht : orderOf t = 2)
    (hab : Commute a b) (hat : Commute a t) (hbt : Commute b t)
    (hne : a ≠ b) (hta : t ≠ a) (htb : t ≠ b) (htab : t ≠ a * b) :
    3 ≤ CFSG.Open.pRank 2 K := by
  have haa : a * a = 1 := by simpa only [ha, pow_two] using pow_orderOf_eq_one a
  have hbb : b * b = 1 := by simpa only [hb, pow_two] using pow_orderOf_eq_one b
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    norm_num at ha
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb
    norm_num at hb
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    norm_num at ht
  let F := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a b haa hbb hab
  have hF : IsKleinFour F := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    a b haa hbb ha1 hb1 hne hab
  have hFmem : ∀ x, x ∈ F ↔ x = a * b ∨ x = a ∨ x = b ∨ x = 1 := by
    intro x
    change x ∈ ({a * b, a, b, 1} : Set G) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hFK : F ≤ K := by
    intro x hx
    rcases (hFmem x).mp hx with rfl | rfl | rfl | rfl
    · exact K.mul_mem haK hbK
    · exact haK
    · exact hbK
    · exact K.one_mem
  have hFelem : IsElemAbelian 2 F := by
    refine ⟨hF.isMulCommutative, fun x hx => ?_⟩
    have hexp : (⟨x, hx⟩ : F) ^ 2 = 1 := by
      rw [← hF.exponent_two]
      exact Monoid.pow_exponent_eq_one _
    exact congrArg Subtype.val hexp
  have htF : t ∉ F := by
    rw [hFmem]
    rintro (h | h | h | h)
    · exact htab h
    · exact hta h
    · exact htb h
    · exact ht1 h
  have htcent : t ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases (hFmem x).mp hx with rfl | rfl | rfl | rfl
    · exact (hat.mul_left hbt).eq
    · exact hat.eq
    · exact hbt.eq
    · simp
  let E := Subgroup.zpowers t ⊔ F
  have hE : IsElemAbelian 2 E :=
    commuting_elementary_sup (Subgroup.zpowers t) F (involution_zpowers_elementary t ht) hFelem
      (Subgroup.zpowers_le.mpr htcent)
  have hEK : E ≤ K := sup_le (Subgroup.zpowers_le.mpr htK) hFK
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hE).exists_card_eq
  have hFE : F ≤ E := le_sup_right
  have hlt : Nat.card F < Nat.card E := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hFE) fun heq => htF ?_
    have hFeq : F = E := Subgroup.eq_of_le_of_card_ge hFE heq.ge
    rw [hFeq]
    exact (le_sup_left : Subgroup.zpowers t ≤ E) (Subgroup.mem_zpowers t)
  rw [hF.card_four, hk] at hlt
  have hk3 : 3 ≤ k := by
    by_contra hsmall
    push Not at hsmall
    interval_cases k <;> norm_num at hlt
  exact hk3.trans (CFSG.SectionRank.le_pRank (by decide) hEK hE hk)

omit [Finite G] in
theorem mem_or_mul_mem_of_mem_closure (N : Subgroup G) {t : G} (ht : t * t = 1)
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) {A : Set G} (hA : ∀ a ∈ A, a * t ∈ N) {x : G}
    (hx : x ∈ Subgroup.closure A) : x ∈ N ∨ x * t ∈ N := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [htinv] at htN
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact Or.inr (hA a ha)
  | one => exact Or.inl N.one_mem
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (N.mul_mem hx hy)
    · exact Or.inr (by simpa only [mul_assoc] using N.mul_mem hx hy)
    · refine Or.inr ?_
      have hmem := N.mul_mem hx (htN y hy)
      have heq : x * t * (t * y * t) = x * y * t := by
        calc x * t * (t * y * t) = x * (t * t) * y * t := by group
          _ = x * y * t := by rw [ht, mul_one]
      rwa [heq] at hmem
    · refine Or.inl ?_
      have hmem := N.mul_mem hx (htN _ hy)
      have heq : x * t * (t * (y * t) * t) = x * y := by
        calc x * t * (t * (y * t) * t) = x * (t * t) * y * (t * t) := by group
          _ = x * y := by rw [ht, mul_one, mul_one]
      rwa [heq] at hmem
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (N.inv_mem hx)
    · refine Or.inr ?_
      have hmem := htN _ (N.inv_mem hx)
      have heq : t * (x * t)⁻¹ * t = x⁻¹ * t := by group
      rwa [heq] at hmem

omit [Finite G] in
theorem conj_mem_localInvolutionPointHull {z u x : G} (g : G)
    (hx : x ∈ localInvolutionPointHull z u) :
    g⁻¹ * x * g ∈ localInvolutionPointHull z (g⁻¹ * u * g) := by
  let φ : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hφ : ∀ y, φ y = g⁻¹ * y * g := fun y => by
    simp [φ]
  have hle : localInvolutionPointHull z u ≤
      (localInvolutionPointHull z (g⁻¹ * u * g)).comap φ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨e, rfl⟩, hyu⟩
    change φ (rightConjugateElem z e) ∈ localInvolutionPointHull z (g⁻¹ * u * g)
    rw [hφ]
    refine mem_localInvolutionPointHull ⟨e * g, ?_⟩ ?_
    · simp only [rightConjugateElem]
      group
    · have hcomm : Commute (rightConjugateElem z e) u :=
        Subgroup.mem_centralizer_singleton_iff.mp hyu
      have := hcomm.map φ
      rwa [hφ, hφ] at this
  have := hle hx
  rwa [Subgroup.mem_comap, hφ] at this

theorem exists_conj_commute_ne (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {u : G} (hu : orderOf u = 2) :
    ∃ g : G, g * u * g⁻¹ * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ≠ u := by
  by_contra hiso
  push Not at hiso
  let : Fintype G := Fintype.ofFinite G
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    norm_num at hu
  have huu : u * u = 1 := by simpa only [hu, pow_two] using pow_orderOf_eq_one u
  obtain ⟨N, hN, hNodd, hNu⟩ := CFSG.ZStar.glauberman_zStar G u hu1 huu hiso
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · have hcenter : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : g * u * g⁻¹ * u⁻¹ = 1 := Subgroup.mem_bot.mp (hbot ▸ hNu g)
      calc g * u = (g * u * g⁻¹ * u⁻¹) * u * g := by group
        _ = u * g := by rw [h1, one_mul]
    rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with hc | hc
    · exact hu1 (Subgroup.mem_bot.mp (hc ▸ hcenter))
    · obtain ⟨a, b, hab⟩ := hnonab
      have ha : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  · have hodd : Odd (Nat.card G) := by
      rw [htop, Subgroup.card_top] at hNodd
      exact hNodd
    have hdvd : orderOf u ∣ Nat.card G := orderOf_dvd_natCard u
    rw [hu] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem not_mem_localHull_of_rank_le_two (S : Sylow 2 G) (H : Subgroup G) (z : G)
    (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
    (hzC : Subgroup.centralizer ({z} : Set G) ≤ H)
    (u : G) (hu : orderOf u = 2) (huS : u ∈ (S : Subgroup G))
    (hsyl : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 P →
      Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) :
        Subgroup G))
    (hrank : CFSG.Open.pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 2)
    (hesc : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    u ∉ localInvolutionPointHull z u := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.centralizer ({u} : Set G)
  set T := (S : Subgroup G) ⊓ M
  have hzH : z ∈ H := hset.sylow_le hz.1
  have huH : u ∈ H := hset.sylow_le huS
  have hzz : z * z = 1 := by simpa only [hz.2.1, pow_two] using pow_orderOf_eq_one z
  have huz : Commute u z := hz.2.2 u huS
  have hnot : ∀ g : G, g⁻¹ * z * g ≠ u := by
    intro g hg
    obtain ⟨h, hh, hhz⟩ := two_generated_core_controls_involution_fusion S H hset.sylow_le
      hset.core_le z hzH hz.2.1 g (hg ▸ huH)
    exact hesc (centralizer_le_of_conj hh (hhz.trans hg) hzC)
  have hne : u ≠ z := fun h => hnot 1 (by rw [h]; group)
  have huM : u ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzM : z ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr huz.eq.symm
  have huT : u ∈ T := ⟨huS, huM⟩
  have hzT : z ∈ T := ⟨hz.1, hzM⟩
  have hTM : T ≤ M := inf_le_right
  have hT2 : IsPGroup 2 T := S.isPGroup'.to_le inf_le_left
  have hconj : ∀ P : Subgroup G, P ≤ M → IsPGroup 2 P → ∃ c ∈ M, ∀ x ∈ P, c⁻¹ * x * c ∈ T :=
    fun P hPM hP => exists_conj_mem_of_card_le hTM hT2 hsyl hPM hP
  have hinv : ∀ t ∈ T, orderOf t = 2 → t = u ∨ t = z ∨ t = u * z := by
    intro t htT ht
    by_contra hcon
    push Not at hcon
    obtain ⟨htu, htz, htuz⟩ := hcon
    have hut : Commute u t := (Subgroup.mem_centralizer_singleton_iff.mp htT.2).symm
    have hzt : Commute z t := (hz.2.2 t htT.1).symm
    have := three_le_pRank_of_commuting_involutions huT hzT htT hu hz.2.1 ht huz hut hzt hne
      htu htz htuz
    omega
  obtain ⟨d, hd⟩ : ∃ d : G, d⁻¹ * u * d = u * z := by
    obtain ⟨g, hgc, hgne⟩ := exists_conj_commute_ne hset.simple hset.nonabelian hu
    have hxM : g * u * g⁻¹ ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr hgc
    have hx : orderOf (g * u * g⁻¹) = 2 := by
      rw [← hu]
      simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq u
    obtain ⟨c, hcM, hc⟩ := hconj _ (Subgroup.zpowers_le.mpr hxM)
      (isPGroup_zpowers_of_orderOf_eq_two hx)
    have hyT := hc _ (Subgroup.mem_zpowers _)
    have hy : orderOf (c⁻¹ * (g * u * g⁻¹) * c) = 2 := by
      rw [← hx]
      simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj c⁻¹).orderOf_eq (g * u * g⁻¹)
    rcases hinv _ hyT hy with h | h | h
    · exfalso
      apply hgne
      have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hcM
      calc g * u * g⁻¹ = c * (c⁻¹ * (g * u * g⁻¹) * c) * c⁻¹ := by group
        _ = c * u * c⁻¹ := by rw [h]
        _ = u := by rw [hcu]; group
    · exfalso
      apply hnot (c⁻¹ * g)
      rw [← h]
      group
    · exact ⟨g⁻¹ * c, by rw [← h]; group⟩
  have hclassT : ∀ e : G, e⁻¹ * z * e ∈ T → e⁻¹ * z * e = z := by
    intro e heT
    have he : orderOf (e⁻¹ * z * e) = 2 := by
      rw [← hz.2.1]
      simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj e⁻¹).orderOf_eq z
    rcases hinv _ heT he with h | h | h
    · exact absurd h (hnot e)
    · exact h
    · exfalso
      apply hnot (e * d⁻¹)
      calc (e * d⁻¹)⁻¹ * z * (e * d⁻¹) = d * (e⁻¹ * z * e) * d⁻¹ := by group
        _ = d * (d⁻¹ * u * d) * d⁻¹ := by rw [h, hd]
        _ = u := by group
  have hMconj : ∀ e : G, e⁻¹ * z * e ∈ M → ∃ c ∈ M, e⁻¹ * z * e = c * z * c⁻¹ := by
    intro e heM
    have he : orderOf (e⁻¹ * z * e) = 2 := by
      rw [← hz.2.1]
      simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj e⁻¹).orderOf_eq z
    obtain ⟨c, hcM, hc⟩ := hconj _ (Subgroup.zpowers_le.mpr heM)
      (isPGroup_zpowers_of_orderOf_eq_two he)
    have h1 : (e * c)⁻¹ * z * (e * c) = z := hclassT (e * c) (by
      convert hc _ (Subgroup.mem_zpowers _) using 1
      group)
    refine ⟨c, hcM, ?_⟩
    calc e⁻¹ * z * e = c * ((e * c)⁻¹ * z * (e * c)) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [h1]
  let : Fintype M := Fintype.ofFinite M
  have hz1 : z ≠ 1 := by
    rintro rfl
    have := hz.2.1
    rw [orderOf_one] at this
    norm_num at this
  obtain ⟨N, hN, hNodd, hNz⟩ := CFSG.ZStar.glauberman_zStar M ⟨z, hzM⟩
    (fun h => hz1 (congrArg Subtype.val h)) (Subtype.ext hzz) (by
      intro m hm
      have hm' : (m : G) * z * (m : G)⁻¹ * z = z * ((m : G) * z * (m : G)⁻¹) :=
        congrArg Subtype.val hm
      apply Subtype.ext
      change (m : G) * z * (m : G)⁻¹ = z
      have haM : (m : G) * z * (m : G)⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem m.property hzM) (M.inv_mem m.property)
      have ha : orderOf ((m : G) * z * (m : G)⁻¹) = 2 := by
        rw [← hz.2.1]
        simpa only [MulAut.conj_apply] using (MulAut.conj (m : G)).orderOf_eq z
      have hP : IsPGroup 2
          (Subgroup.zpowers ((m : G) * z * (m : G)⁻¹) ⊔ Subgroup.zpowers z : Subgroup G) :=
        isPGroup_of_isElemAbelian (commuting_elementary_sup _ _
          (involution_zpowers_elementary _ ha) (involution_zpowers_elementary z hz.2.1)
          (zpowers_le_centralizer_zpowers hm'))
      obtain ⟨c, hcM, hc⟩ := hconj _
        (sup_le (Subgroup.zpowers_le.mpr haM) (Subgroup.zpowers_le.mpr hzM)) hP
      have h1 : c⁻¹ * ((m : G) * z * (m : G)⁻¹) * c = z := by
        have hmem := hc _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        have := hclassT ((m : G)⁻¹ * c) (by convert hmem using 1; group)
        calc c⁻¹ * ((m : G) * z * (m : G)⁻¹) * c
            = ((m : G)⁻¹ * c)⁻¹ * z * ((m : G)⁻¹ * c) := by group
          _ = z := this
      have h2 : c⁻¹ * z * c = z :=
        hclassT c (hc _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
      have h3 : c⁻¹ * ((m : G) * z * (m : G)⁻¹) * c = c⁻¹ * z * c := h1.trans h2.symm
      simpa using h3)
  set NG := N.map M.subtype with hNG
  have hNGodd : Odd (Nat.card NG) := by
    rw [hNG, Subgroup.card_map_of_injective M.subtype_injective]
    exact hNodd
  have hnorm : ∀ n ∈ NG, z * n * z⁻¹ ∈ NG := by
    rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨z, hzM⟩ * n * ⟨z, hzM⟩⁻¹, hN.conj_mem n hn _, rfl⟩
  have hgen : ∀ a ∈ involutionPointClass z ∩ (M : Set G), a * z ∈ NG := by
    rintro a ⟨⟨e, rfl⟩, haM⟩
    obtain ⟨c, hcM, hc⟩ := hMconj e haM
    refine Subgroup.mem_map.mpr ⟨⟨c, hcM⟩ * ⟨z, hzM⟩ * ⟨c, hcM⟩⁻¹ * ⟨z, hzM⟩⁻¹,
      hNz ⟨c, hcM⟩, ?_⟩
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    change c * z * c⁻¹ * z⁻¹ = rightConjugateElem z e * z
    rw [hzinv, rightConjugateElem, hc]
  intro huL
  rcases mem_or_mul_mem_of_mem_closure NG hzz hnorm hgen huL with h | h
  · exact not_odd_card_of_orderOf_eq_two h hu hNGodd
  · have huz2 : orderOf (u * z) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two, mul_assoc, ← mul_assoc z u z, ← huz.eq, mul_assoc, hzz, mul_one,
          ← pow_two, ← hu, pow_orderOf_eq_one]
      · intro h1
        apply hne
        have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
        rw [← hzinv]
        exact eq_inv_of_mul_eq_one_left h1
    exact not_odd_card_of_orderOf_eq_two h huz2 hNGodd

theorem escapingCentralizerStep_of_sylow_placed (h : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2
    G) (H : Subgroup G) (z : G), CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
    Subgroup.centralizer ({z} : Set G) ≤ H → ∀ u : G, orderOf u = 2 → u ∈ (S : Subgroup G) → (∀ P :
    Subgroup G, P ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 P → Nat.card P ≤ Nat.card ((S :
    Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G)) → ¬ Subgroup.centralizer ({u} :
    Set G) ≤ H → u ∉ localInvolutionPointHull z u) :
    EscapingCentralizerStep := by
  intro G _ _ S H z hset hz hzC u hu huz hesc
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.centralizer ({u} : Set G)
  have huM : u ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hU : IsPGroup 2 (Subgroup.zpowers (⟨u, huM⟩ : M)) :=
    isPGroup_zpowers_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hu])
  obtain ⟨Q, hUQ⟩ := hU.exists_le_sylow
  set QG := (Q : Subgroup M).map M.subtype
  have huQG : u ∈ QG := Subgroup.mem_map.mpr ⟨⟨u, huM⟩, hUQ (Subgroup.mem_zpowers _), rfl⟩
  have hQGM : QG ≤ M := Subgroup.map_subtype_le _
  have hQGcard : Nat.card QG = Nat.card Q := Subgroup.card_map_of_injective M.subtype_injective
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow S (Q.isPGroup'.map M.subtype)
  have hu'S : g⁻¹ * u * g ∈ (S : Subgroup G) := hg u huQG
  have hu' : orderOf (g⁻¹ * u * g) = 2 := by
    rw [← hu]
    simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq u
  have huH : u ∈ H := hzC (Subgroup.mem_centralizer_singleton_iff.mpr huz.eq)
  have hesc' : ¬ Subgroup.centralizer ({g⁻¹ * u * g} : Set G) ≤ H := by
    intro hle
    obtain ⟨k, hk, hku⟩ := two_generated_core_controls_involution_fusion S H hset.sylow_le
      hset.core_le u huH hu g (hset.sylow_le hu'S)
    refine hesc (centralizer_le_of_conj (H.inv_mem hk) ?_ hle)
    rw [← hku]
    group
  have hsyl : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({g⁻¹ * u * g} : Set G) →
      IsPGroup 2 P → Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓
        Subgroup.centralizer ({g⁻¹ * u * g} : Set G) : Subgroup G) := by
    intro P hP hP2
    have hP'M : P.map (MulAut.conj g).toMonoidHom ≤ M := by
      rintro _ ⟨x, hx, rfl⟩
      have hxc : x * (g⁻¹ * u * g) = (g⁻¹ * u * g) * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hP hx)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change g * x * g⁻¹ * u = u * (g * x * g⁻¹)
      calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [hxc]
        _ = u * (g * x * g⁻¹) := by group
    have h1 := card_le_card_sylow_of_le Q hP'M (hP2.map _)
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h1
    have hQ'le : QG.map (MulAut.conj g⁻¹).toMonoidHom ≤
        (S : Subgroup G) ⊓ Subgroup.centralizer ({g⁻¹ * u * g} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxS : g⁻¹ * x * g ∈ (S : Subgroup G) := hg x hx
      have hxc : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hQGM hx)
      change g⁻¹ * x * g⁻¹⁻¹ ∈ _
      rw [inv_inv]
      refine Subgroup.mem_inf.mpr ⟨hxS, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * x * g * (g⁻¹ * u * g) = g⁻¹ * (x * u) * g := by group
        _ = g⁻¹ * (u * x) * g := by rw [hxc]
        _ = g⁻¹ * u * g * (g⁻¹ * x * g) := by group
    have h2 := Subgroup.card_le_of_le hQ'le
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hQGcard] at h2
    omega
  have hnot := h G S H z hset hz hzC (g⁻¹ * u * g) hu' hu'S hsyl hesc'
  exact fun huL => hnot (conj_mem_localInvolutionPointHull g huL)

open scoped commutatorElement in
theorem CoreSetting.isPerfect {S : Sylow 2 G} {H : Subgroup G} (hset : CoreSetting G S H) :
    Group.IsPerfect G := by
  have := hset.simple
  refine ⟨?_⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hset.nonabelian
    have hmem : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hab hmem
  · exact h

theorem three_le_pRank_of_sylow_placed {S : Sylow 2 G} {H : Subgroup G}
    (hset : CoreSetting G S H) {u : G} (hu : orderOf u = 2)
    (hsyl : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 P →
      Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) :
        Subgroup G)) :
    3 ≤ CFSG.Open.pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsPerfect G := hset.isPerfect
  set M := Subgroup.centralizer ({u} : Set G)
  have hTM : (S : Subgroup G) ⊓ M ≤ M := inf_le_right
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_subgroupOf hTM (S.isPGroup'.to_le inf_le_left) hsyl
  have hQT : (Q : Subgroup M).map M.subtype = (S : Subgroup G) ⊓ M := by
    rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTM]
  have hG : 3 ≤ CFSG.Open.twoRank G := by
    rw [← sylow_two_rank_eq S]
    exact hset.rank
  rw [← hQT, sylow_image_two_rank_eq M Q,
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by decide) M]
  exact perfect_involution_centralizer_rank_three hG u hu

theorem escapingCentralizerStep_of_highRank (h : HighRankEscapingStep) :
    EscapingCentralizerStep := by
  refine escapingCentralizerStep_of_sylow_placed ?_
  intro G _ _ S H z hset hz hzC u hu huS hsyl hesc
  exact h G S H z hset hz hzC u hu huS hsyl (three_le_pRank_of_sylow_placed hset hu hsyl) hesc

end CFSG.ProperTwoGeneratedCore.Assembly

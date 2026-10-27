module

public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Proof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28End

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.AGLEmbedding (CatalogSimpleSections)

variable {Y : Type} [Group Y]

structure FData (F U : Subgroup Y) (x : Y) : Prop where
  card_F : Nat.card F = 3 ^ 3
  nonab : ¬ IsMulCommutative F
  U_le : U ≤ F
  U_elem : IsElemAbelian 3 U
  U_card : Nat.card U = 3 ^ 2
  omega : ∀ f ∈ F, f ^ 3 = 1 → f ∈ U
  x_mem : x ∈ U
  x_ne : x ≠ 1
  x_cent : ∀ f ∈ F, f * x = x * f

namespace FData

variable [Finite Y] {F U : Subgroup Y} {x : Y}

theorem U_comm (h : FData F U x) {a b : Y} (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a := by
  have := h.U_elem.1
  exact setLike_mul_comm (s := U) ha hb

theorem x_pow (h : FData F U x) : x ^ 3 = 1 := h.U_elem.2 x h.x_mem

theorem orderOf_x (h : FData F U x) : orderOf x = 3 := orderOf_eq_prime h.x_pow h.x_ne

theorem exists_u (h : FData F U x) : ∃ u ∈ U, u ∉ zpowers x := by
  by_contra hall
  push Not at hall
  have h2 := Subgroup.card_le_of_le (show U ≤ zpowers x from hall)
  rw [h.U_card, Nat.card_zpowers, h.orderOf_x] at h2
  norm_num at h2

theorem exists_not_mem (h : FData F U x) : ∃ t ∈ F, t ∉ U := by
  by_contra hall
  push Not at hall
  have h2 := Subgroup.card_le_of_le (show F ≤ U from hall)
  rw [h.card_F, h.U_card] at h2
  norm_num at h2

theorem pow_ne_one (h : FData F U x) {t : Y} (ht : t ∈ F) (htU : t ∉ U) : t ^ 3 ≠ 1 :=
  fun h3 => htU (h.omega t ht h3)

theorem card_central_le (h : FData F U x) {S : Subgroup Y} (hSF : S ≤ F)
    (hS : ∀ s ∈ S, ∀ f ∈ F, f * s = s * f) : Nat.card S ≤ 3 := by
  by_contra hlt
  push Not at hlt
  have hSZ : S.subgroupOf F ≤ center F := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro f
    exact Subtype.ext (hS _ hs f f.2)
  have h1 : Nat.card S ≤ Nat.card (center F) :=
    calc Nat.card S = Nat.card (S.subgroupOf F) :=
          (Nat.card_congr (subgroupOfEquivOfLe hSF).toEquiv).symm
      _ ≤ Nat.card (center F) := Subgroup.card_le_of_le hSZ
  have hZ27 : Nat.card (center F) ∣ 3 ^ 3 := h.card_F ▸ Subgroup.card_subgroup_dvd_card (center F)
  obtain ⟨i, hi, hZ⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hZ27
  rw [hZ] at h1
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (center F)
  rw [h.card_F, hZ] at hq
  have hcyc : IsCyclic (↥F ⧸ center ↥F) := by
    interval_cases i
    · norm_num at h1; omega
    · norm_num at h1; omega
    · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card (p := 3) (by omega)
    · have h1' : Nat.card (↥F ⧸ center ↥F) = 1 := by omega
      haveI : Subsingleton (↥F ⧸ center ↥F) := (Nat.card_eq_one_iff_unique.mp h1').1
      infer_instance
  exact h.nonab (IsMulCommutative.of_comm (commutative_of_cyclic_center_quotient
    (QuotientGroup.mk' (center ↥F)) (by rw [QuotientGroup.ker_mk'])))

theorem false_of_central (h : FData F U x) {a b : Y} (ha : a ∈ U) (hb : b ∈ U) (ha1 : a ≠ 1)
    (hba : b ∉ zpowers a) (hac : ∀ f ∈ F, f * a = a * f) (hbc : ∀ f ∈ F, f * b = b * f) :
    False := by
  have ha3 : a ^ 3 = 1 := h.U_elem.2 a ha
  have hb3 : b ^ 3 = 1 := h.U_elem.2 b hb
  have hab : ∀ e ∈ zpowers a, e * b = b * e := by
    intro e he
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute a b from h.U_comm ha hb) i).eq
  have hcard : Nat.card (zpowers a ⊔ zpowers b : Subgroup Y) = 9 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers a) hb3 hba hab,
      Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hle : (zpowers a ⊔ zpowers b : Subgroup Y) ≤ F :=
    sup_le (zpowers_le.mpr (h.U_le ha)) (zpowers_le.mpr (h.U_le hb))
  have hc := h.card_central_le hle (fun s hs f hf => by
    have : zpowers a ⊔ zpowers b ≤ centralizer ({f} : Set Y) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hac f hf).symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hbc f hf).symm))
    exact (mem_centralizer_singleton_iff.mp (this hs)).symm)
  omega

theorem sup_eq (h : FData F U x) {t : Y} (ht : t ∈ F) (htU : t ∉ U) : U ⊔ zpowers t = F := by
  have hle : U ⊔ zpowers t ≤ F := sup_le h.U_le (zpowers_le.mpr ht)
  have h9 : 3 ^ 2 ∣ Nat.card (U ⊔ zpowers t : Subgroup Y) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : U ≤ U ⊔ zpowers t)
    rwa [h.U_card] at this
  have h27 : Nat.card (U ⊔ zpowers t : Subgroup Y) ∣ 3 ^ 3 :=
    h.card_F ▸ Subgroup.card_dvd_of_le hle
  have hne : Nat.card (U ⊔ zpowers t : Subgroup Y) ≠ 3 ^ 2 := by
    intro h9'
    have : U = U ⊔ zpowers t :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h9', h.U_card])
    exact htU (this ▸ mem_sup_right (mem_zpowers t))
  have hc : Nat.card (U ⊔ zpowers t : Subgroup Y) = 3 ^ 3 := by
    obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h27
    rw [hc] at h9 hne ⊢
    interval_cases i <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, h.card_F])

theorem not_comm (h : FData F U x) {u t : Y} (hu : u ∈ U) (hux : u ∉ zpowers x) (ht : t ∈ F)
    (htU : t ∉ U) : u * t ≠ t * u := by
  intro hcomm
  have hsup := h.sup_eq ht htU
  have hcent : ∀ f ∈ F, f * u = u * f := by
    intro f hf
    rw [← hsup] at hf
    have : U ⊔ zpowers t ≤ centralizer ({u} : Set Y) :=
      sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (h.U_comm ha hu))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcomm.symm))
    exact mem_centralizer_singleton_iff.mp (this hf)
  exact h.false_of_central h.x_mem hu h.x_ne hux h.x_cent hcent

theorem exists_pow_order_three {b : Y} (hb1 : b ≠ 1) {n : ℕ} (hb : b ^ 3 ^ n = 1) :
    ∃ m : ℕ, b ^ m ≠ 1 ∧ (b ^ m) ^ 3 = 1 := by
  induction n with
  | zero => exact absurd (by simpa using hb) hb1
  | succ n ih =>
    by_cases h : b ^ 3 ^ n = 1
    · exact ih h
    · exact ⟨3 ^ n, h, by rw [← pow_mul, ← pow_succ]; exact hb⟩

theorem exists_central (hF : IsPGroup 3 F) {A : Subgroup Y} (hAF : A ≤ F)
    (hAn : ∀ f ∈ F, ∀ a ∈ A, f * a * f⁻¹ ∈ A) (hne : A ≠ ⊥) :
    ∃ z ∈ A, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ f ∈ F, f * z = z * f := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent F := hF.isNilpotent
  haveI : (A.subgroupOf F).Normal :=
    ⟨fun a ha f => by
      rw [mem_subgroupOf] at ha ⊢
      exact hAn f f.2 a ha⟩
  have hne' : A.subgroupOf F ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have h1 : (⟨a, hAF ha⟩ : F) ∈ A.subgroupOf F := ha
    rw [h, mem_bot] at h1
    exact mem_bot.mpr (congrArg Subtype.val h1)
  obtain ⟨b, hb⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  have hb1 : ((b : F) : Y) ≠ 1 := fun h1 => hb (Subtype.ext (Subtype.ext h1))
  obtain ⟨n, hn⟩ := hF (b : F)
  obtain ⟨m, hm1, hm3⟩ := exists_pow_order_three hb1 (n := n) (congrArg Subtype.val hn)
  have hbA : ((b : F) : Y) ∈ A := mem_subgroupOf.mp b.2.1
  have hbc : ∀ f ∈ F, f * ((b : F) : Y) = ((b : F) : Y) * f := fun f hf =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp b.2.2 ⟨f, hf⟩)
  exact ⟨((b : F) : Y) ^ m, pow_mem hbA m, hm1, hm3, fun f hf =>
    (Commute.pow_right (show Commute f ((b : F) : Y) from hbc f hf) m).eq⟩

end FData

section EndData

variable [Finite Y]

structure EndData (F U M₁ N R : Subgroup Y) (x : Y) : Prop where
  toFData : FData F U x
  catalog : CatalogSimpleSections Y
  sylow : IsSylowOf 3 F ⊤
  F_le : F ≤ M₁
  cover : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set Y) ≤ M₁
  N_le : N ≤ M₁
  N_norm : ∀ m ∈ M₁, ∀ n ∈ N, m * n * m⁻¹ ∈ N
  N_cop : ¬ 3 ∣ Nat.card N
  R_le : R ≤ N
  R_two : IsPGroup 2 R
  R_norm : U ≤ normalizer (R : Set Y)

namespace EndData

variable {F U M₁ N R : Subgroup Y} {x : Y}

theorem exists_sylow (hd : EndData F U M₁ N R x) : ∃ S : Sylow 3 Y, (S : Subgroup Y) = F := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hp, hidx⟩ := isSylowOf_iff.mp hd.sylow
  rw [Subgroup.relIndex_top_right] at hidx
  exact ⟨hp.toSylow hidx, rfl⟩

theorem card_elem_le (hd : EndData F U M₁ N R x) {E : Subgroup Y} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := elementary_isPGroup 3 E hE
  obtain ⟨k, -, hk⟩ := GL83P3L28Aux.exists_mem_conj_le_sylow hd.sylow le_top hEp
  have hmem : ∀ y : E, k⁻¹ * (y : Y) * k ∈ U := fun y => by
    refine hd.toFData.omega _ (hk y y.2) ?_
    have h3 := hE.2 y y.2
    calc (k⁻¹ * (y : Y) * k) ^ 3 = k⁻¹ * (y : Y) ^ 3 * k := by
          have := conj_pow (a := k⁻¹) (b := (y : Y)) (i := 3)
          simpa using this
      _ = 1 := by rw [h3]; group
  let f : E → U := fun y => ⟨k⁻¹ * y * k, hmem y⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : k⁻¹ * (a : Y) * k = k⁻¹ * (b : Y) * k := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h1)
  calc Nat.card E ≤ Nat.card U := Nat.card_le_card_of_injective f hf
    _ = 9 := by rw [hd.toFData.U_card]; norm_num

theorem pRank_le_two (hd : EndData F U M₁ N R x) :
    CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3
    Nat.prime_three (⊤ : Subgroup Y)
  have h1 := hd.card_elem_le hE
  rw [hcard] at h1
  by_contra hlt
  push Not at hlt
  have h2 : 3 ^ 3 ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
    Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem comm_mem_inf (hd : EndData F U M₁ N R x) {A : Subgroup Y} [A.Normal] {n e : Y}
    (hn : n ∈ N) (he : e ∈ M₁) (heA : e ∈ A) : n * e * n⁻¹ * e⁻¹ ∈ N ⊓ A := by
  refine ⟨?_, ?_⟩
  · have h1 := hd.N_norm e he n⁻¹ (N.inv_mem hn)
    have : n * e * n⁻¹ * e⁻¹ = n * (e * n⁻¹ * e⁻¹) := by group
    rw [this]
    exact N.mul_mem hn h1
  · exact A.mul_mem (Normal.conj_mem ‹A.Normal› e heA n) (A.inv_mem heA)

theorem eq_bot_of_noComponent (hd : EndData F U M₁ N R x)
    (hcore : primeComplementCore (G := Y) 3 = ⊥) (hno : ∀ K : Subgroup Y, ¬ IsComponentOf K ⊤) :
    N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := hd.exists_sylow
  have hlay : CFSG.layer Y = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall
    (fun K hK => hno K ((CFSG.isComponent_iff_open K).mp hK))
  have hFit : CFSG.fittingSubgroup Y = CFSG.pCore 3 Y := CFSG.Fitting_eq_pcore Y 3 hcore
  have hC : centralizer (CFSG.pCore 3 Y : Set Y) ≤ CFSG.pCore 3 Y := by
    have := CFSG.centralizer_generalizedFitting_le Y
    rwa [CFSG.generalizedFitting.eq_sup, hlay, hFit, sup_bot_eq] at this
  have hOF : CFSG.pCore 3 Y ≤ F := by
    have := CFSG.pCore_isPGroup.le_sylow_of_normal S
    rwa [hS] at this
  have hbot : CFSG.pCore 3 Y ⊓ N = ⊥ :=
    CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hd.N_cop CFSG.pCore_isPGroup
  rw [eq_bot_iff]
  intro n hn
  have hnC : n ∈ centralizer (CFSG.pCore 3 Y : Set Y) := by
    rw [mem_centralizer_iff]
    intro e he
    have hcomm := hd.comm_mem_inf (A := CFSG.pCore 3 Y) hn (hd.F_le (hOF he)) he
    rw [inf_comm, hbot, mem_bot, mul_inv_eq_one] at hcomm
    calc e * n = (n * e * n⁻¹) * n := by rw [hcomm]
      _ = n * e := by group
  have := hbot ▸ (mem_inf.mpr ⟨hC hnC, hn⟩ : n ∈ CFSG.pCore 3 Y ⊓ N)
  exact this

theorem eq_bot_of_cover (hd : EndData F U M₁ N R x) {K : Subgroup Y} [K.Normal]
    (hKs : IsSimpleGroup K) (h3K : 3 ∣ Nat.card K) (hKM : K ≤ M₁)
    (hCK : centralizer (K : Set Y) = ⊥) : N = ⊥ := by
  have hA : N ⊓ K = ⊥ := by
    haveI : ((N ⊓ K).subgroupOf K).Normal := ⟨fun a ha k => by
      rw [mem_subgroupOf] at ha ⊢
      exact ⟨hd.N_norm k (hKM k.2) a ha.1, K.mul_mem (K.mul_mem k.2 a.2) (K.inv_mem k.2)⟩⟩
    rcases hKs.eq_bot_or_eq_top_of_normal ((N ⊓ K).subgroupOf K) with h | h
    · rw [eq_bot_iff]
      intro y hy
      have h1 : (⟨y, hy.2⟩ : K) ∈ (N ⊓ K).subgroupOf K := hy
      rw [h, mem_bot] at h1
      exact mem_bot.mpr (congrArg Subtype.val h1)
    · exfalso
      have hKN : K ≤ N := fun k hk => (subgroupOf_eq_top.mp h hk).1
      exact hd.N_cop (h3K.trans (Subgroup.card_dvd_of_le hKN))
  rw [eq_bot_iff]
  intro n hn
  have : n ∈ centralizer (K : Set Y) := by
    rw [mem_centralizer_iff]
    intro k hk
    have hcomm := hd.comm_mem_inf (A := K) hn (hKM hk) hk
    rw [hA, mem_bot, mul_inv_eq_one] at hcomm
    calc k * n = (n * k * n⁻¹) * n := by rw [hcomm]
      _ = n * k := by group
  rwa [hCK] at this

end EndData

end EndData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28End

module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBlocks
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem d1_exists_card_le_of_conj_mem_zpowers {X : Type} [Group X] [Finite X]
    {E : Subgroup X} (hE : IsElemAbelian 3 E) {z w : X} (hz3 : z ^ 3 = 1) (hwo : orderOf w = 3)
    (hwE : ∀ e ∈ E, Commute w e)
    (hEz : ∀ e ∈ E, e * z * e⁻¹ * z⁻¹ ∈ Subgroup.zpowers w) :
    ∃ F : Subgroup X, F ≤ Subgroup.centralizer ({z} : Set X) ∧ IsElemAbelian 3 F ∧
      Nat.card E ≤ Nat.card F := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWc : ∀ x ∈ Subgroup.zpowers w, ∀ e ∈ E, Commute x e := by
    intro x hx e he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hwE e he).zpow_left n
  let φ : E →* Subgroup.zpowers w :=
    { toFun := fun e => ⟨e * z * e⁻¹ * z⁻¹, hEz e e.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hEz b b.2)
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hEz a a.2)
        have hb' : (b : X) * z * (b : X)⁻¹ = w ^ n * z := by rw [hn]; group
        have hwa : Commute (w ^ n) (a : X) := (hwE a a.2).zpow_left n
        show ((a : X) * b) * z * ((a : X) * b)⁻¹ * z⁻¹ =
          ((a : X) * z * (a : X)⁻¹ * z⁻¹) * ((b : X) * z * (b : X)⁻¹ * z⁻¹)
        calc ((a : X) * b) * z * ((a : X) * b)⁻¹ * z⁻¹
            = (a : X) * ((b : X) * z * (b : X)⁻¹) * (a : X)⁻¹ * z⁻¹ := by group
          _ = ((a : X) * w ^ n) * z * (a : X)⁻¹ * z⁻¹ := by rw [hb']; group
          _ = (w ^ n * (a : X)) * z * (a : X)⁻¹ * z⁻¹ := by rw [← hwa.eq]
          _ = w ^ n * ((a : X) * z * (a : X)⁻¹ * z⁻¹) := by group
          _ = ((a : X) * z * (a : X)⁻¹ * z⁻¹) * ((b : X) * z * (b : X)⁻¹ * z⁻¹) := by
              rw [← hm, ← hn, (Commute.zpow_zpow_self w n m).eq] }
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range ≤ 3 := by
    have := Subgroup.card_le_of_le (le_top : φ.range ≤ ⊤)
    rw [Subgroup.card_top, Nat.card_zpowers, hwo] at this
    exact this
  set K : Subgroup X := φ.ker.map E.subtype with hK
  have hKc : Nat.card K = Nat.card φ.ker := Subgroup.card_map_of_injective E.subtype_injective
  have hKE : K ≤ E := Subgroup.map_subtype_le _
  have hKz : K ≤ Subgroup.centralizer ({z} : Set X) := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : (e : X) * z * (e : X)⁻¹ * z⁻¹ = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp he)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : (e : X) * z = z * e := by
      calc (e : X) * z = ((e : X) * z * (e : X)⁻¹ * z⁻¹) * (z * e) := by group
        _ = z * e := by rw [h1, one_mul]
    exact h2
  have hKe : IsElemAbelian 3 K := d1_isElemAbelian_of_le hE hKE
  have hEK : Nat.card E ≤ Nat.card K * 3 := by
    rw [hKc, ← hcard]
    exact Nat.mul_le_mul_left _ hrange
  by_cases hzE : z ∈ E
  · refine ⟨E, fun e he => ?_, hE, le_rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨z, hzE⟩)
  · have hzK : z ∉ K := fun h => hzE (hKE h)
    obtain ⟨hFc, hFe⟩ := card_sup_zpowers_elem le_rfl hz3 hzK hKz hKe
    refine ⟨K ⊔ Subgroup.zpowers z, sup_le hKz ?_, hFe, ?_⟩
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · rw [hFc]
      exact hEK

theorem exists_mem_commutator_center {X : Type*} [Group X] [Finite X] {Y : Subgroup X}
    (hY : IsPGroup 3 Y) {a b : X} (ha : a ∈ Y) (hb : b ∈ Y) (hab : a * b ≠ b * a) :
    ∃ e ∈ ⁅Y, Y⁆, e ≠ 1 ∧ e ^ 3 = 1 ∧ ∀ y ∈ Y, Commute e y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent ↥Y := hY.isNilpotent
  set N : Subgroup ↥Y := ⁅(⊤ : Subgroup ↥Y), ⊤⁆ with hN
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hab
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
    have hc := Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top (⟨a, ha⟩ : ↥Y)))
      (⟨b, hb⟩ : ↥Y) (Subgroup.mem_top _)
    exact (congrArg Subtype.val hc).symm
  have hNc := Group.IsNilpotent.inf_center_ne_bot_of_normal hNne
  set K := N ⊓ Subgroup.center ↥Y with hK
  have hK3 : IsPGroup 3 K := hY.to_subgroup K
  have hKnt : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hNc
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK3
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card_iff_nontrivial.mpr hKnt
    rw [hk] at this
    norm_num at this
  have h3 : 3 ∣ Nat.card K := by rw [hk]; exact dvd_pow_self 3 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx; norm_num at hx
  refine ⟨(((x : K) : ↥Y) : X), ?_, ?_, ?_, ?_⟩
  · have hmap : N.map Y.subtype = ⁅Y, Y⁆ := by
      rw [hN, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ (x : K).2.1
  · intro h1
    exact hx1 (Subtype.ext (Subtype.ext h1))
  · have := congrArg (fun y : K => ((y : ↥Y) : X)) hx3
    simpa using this
  · intro y hy
    have hz := Subgroup.mem_center_iff.mp (x : K).2.2 ⟨y, hy⟩
    exact (congrArg Subtype.val hz).symm

theorem conj_center_data {X : Type*} [Group X] {A : Subgroup X} {ζ : X} (g : X) (hζA : ζ ∈ A)
    (hζC : ζ ∈ Subgroup.centralizer (A : Set X)) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    g * ζ * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom ∧
      g * ζ * g⁻¹ ∈ Subgroup.centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup X) :
        Set X) ∧ (g * ζ * g⁻¹) ^ 3 = 1 ∧ g * ζ * g⁻¹ ≠ 1 := by
  refine ⟨⟨ζ, hζA, by simp [MulAut.conj_apply]⟩, conj_mem_centralizer_map hζC, ?_, ?_⟩
  · rw [conj_pow, hζ3, mul_one, mul_inv_cancel]
  · intro h1
    apply hζ1
    have : ζ = g⁻¹ * (g * ζ * g⁻¹) * g := by group
    rw [this, h1]
    group

variable {G : Type} [Group G] [Finite G]

theorem d1_exists_conj_not_mem_zpowers {P : Sylow 3 G} {z w : G} (hz3 : z ^ 3 = 1)
    (hwo : orderOf w = 3) (hwP : ∀ g ∈ (P : Subgroup G), Commute w g)
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    (hP4 : 4 ≤ Open.pRank 3 (P : Subgroup G)) :
    ∃ g ∈ (P : Subgroup G), g * z * g⁻¹ * z⁻¹ ∉ Subgroup.zpowers w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨E, hEP, hEe, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (P : Subgroup G)
  obtain ⟨F, hFz, hFe, hEF⟩ := d1_exists_card_le_of_conj_mem_zpowers hEe hz3 hwo
    (fun e he => hwP e (hEP he)) (fun e he => hcon e (hEP he))
  have h81 : 3 ^ 4 ≤ Nat.card E := by
    rw [hEc]
    exact Nat.pow_le_pow_right (by norm_num) hP4
  have := hrk F hFz hFe
  omega

theorem card_le_of_le_centralizer_barM_pgroup {M : Subgroup G} {z : G} (hzM : z ∈ M)
    (hz3 : z ^ 3 = 1) {n : ℕ} (hrk : ∀ T : Subgroup G, T ≤ Subgroup.centralizer ({z} : Set G) →
      IsPGroup 3 T → Nat.card T ≤ n)
    {Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hYC : Y ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hY : IsPGroup 3 Y) : Nat.card Y ≤ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zM : M := ⟨z, hzM⟩ with hzMdef
  set C := Subgroup.centralizer ({zM} : Set M) with hC
  set Cb := Subgroup.centralizer ({mk zM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hj]
    exact Nat.Coprime.pow_right j (by norm_num)
  have hzM3 : zM ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  have hzMp : IsPGroup 3 (Subgroup.zpowers zM) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hzM3)
  have hmapC : ∀ c : C, mk (c : M) ∈ Cb := fun c => by
    rw [hCb, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp c.2]
  let f : C →* Cb := (mk.comp C.subtype).codRestrict Cb hmapC
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg, hgx⟩ := exists_mem_centralizer_mk_eq Nat.prime_three (CFSG.pCore 2 ↥M) hcop
      hzMp x.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩
  set Y' := Y.subgroupOf Cb with hY'
  have hY'3 : IsPGroup 3 Y' := hY.comap_subtype
  obtain ⟨T, hT3, hTY⟩ := exists_isPGroup_map_eq' hf hY'3
  set T₂ : Subgroup G := (T.map C.subtype).map M.subtype with hT₂
  have hT₂C : T₂ ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp a.2
    exact congrArg Subtype.val this
  have hT₂3 : IsPGroup 3 T₂ := (hT3.map _).map _
  have hcard : Nat.card Y ≤ Nat.card T₂ := by
    rw [hT₂, Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective C.subtype_injective]
    have h1 : Nat.card Y = Nat.card Y' :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv).symm
    rw [h1, ← hTY]
    exact Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective T)
  exact hcard.trans (hrk T₂ hT₂C hT₂3)

end CFSG.AGLEmbedding

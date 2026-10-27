module

public import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicSubgroupCharacteristic
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt

open CFSG.GorensteinWalter CFSG.Walter

namespace G54

open CFSG.Goldschmidt.G53

variable {G : Type} [Group G] [Finite G]

structure Hyp54 (p : ℕ) (a : G) (H : Subgroup G) : Prop where
  coatom : IsCoatom H
  centralizer_le : Subgroup.centralizer ({a} : Set G) ≤ H
  comm : ⁅qCoreOf H p, Subgroup.zpowers a⁆ ≠ ⊥
  cent : qCoreOf H p ⊓ Subgroup.centralizer ({a} : Set G) ≤
    qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G)
  cyc : IsCyclic (qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G) : Subgroup G)

omit [Finite G] in
theorem map_conj_centralizer (g : G) (K : Subgroup G) :
    (Subgroup.centralizer (K : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [map_centralizer_mulEquiv, Subgroup.coe_map]
  rfl

theorem Hyp54.conj {p : ℕ} {a : G} {H : Subgroup G} (h : Hyp54 p a H) (g : G) :
    Hyp54 p (g * a * g⁻¹) (H.map (MulAut.conj g).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hP : qCoreOf (H.map (MulAut.conj g).toMonoidHom) p =
      (qCoreOf H p).map (MulAut.conj g).toMonoidHom := qCoreOf_conjugateSubgroup H g p
  have hfa : (MulAut.conj g).toMonoidHom a = g * a * g⁻¹ := rfl
  have hZ : qCoreOf (H.map (MulAut.conj g).toMonoidHom) p ⊓
      Subgroup.centralizer (qCoreOf (H.map (MulAut.conj g).toMonoidHom) p : Set G) =
      (qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G)).map
        (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, map_conj_centralizer, hP]
  refine ⟨isCoatom_map_conj g h.coatom, ?_, ?_, ?_, ?_⟩
  · rw [← map_conj_centralizer_singleton]
    exact Subgroup.map_mono h.centralizer_le
  · rw [hP, ← hfa, ← MonoidHom.map_zpowers, ← Subgroup.map_commutator, Ne,
      Subgroup.map_eq_bot_iff_of_injective _ hinj]
    exact h.comm
  · rw [hZ, ← map_conj_centralizer_singleton, hP, ← Subgroup.map_inf_eq _ _ _ hinj]
    exact Subgroup.map_mono h.cent
  · rw [hZ]
    have := h.cyc
    exact isCyclic_of_surjective
      ((qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G)).equivMapOfInjective _
        hinj).toMonoidHom (MulEquiv.surjective _)

theorem le_normalizer_center (H : Subgroup G) (p : ℕ) :
    H ≤ Subgroup.normalizer ((qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G) :
      Subgroup G) : Set G) := fun _ hh =>
  mem_normalizer_inf (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) hh)
    (normalizer_le_normalizer_centralizer_subgroup _
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) hh))

theorem normalizer_zpowers_eq (hsimple : IsSimpleGroup G) {p : ℕ} {a : G} {H : Subgroup G}
    (h : Hyp54 p a H) {y : G}
    (hy : y ∈ qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G)) (hy1 : y ≠ 1) :
    Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) = H := by
  have hyZ : Subgroup.zpowers y ≤ qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G) :=
    Subgroup.zpowers_le.mpr hy
  have hle : H ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
    (le_normalizer_center H p).trans (normalizer_le_normalizer_of_le_cyclic h.cyc hyZ)
  have hyH : Subgroup.zpowers y ≤ H := hyZ.trans (inf_le_left.trans (qCoreOf_le H p))
  have hne := normalizer_ne_top_of_le_isCoatom hsimple h.coatom hyH
    (by rwa [Ne, Subgroup.zpowers_eq_bot])
  rcases h.coatom.le_iff.mp hle with h1 | h1
  · exact absurd h1 hne
  · exact h1

omit [Finite G] in
theorem conj_ne_self_of_conj_eq_inv {e y : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hyo : orderOf y = p) (hinv : e * y * e⁻¹ = y⁻¹) : e * y * e⁻¹ ≠ y := by
  intro h
  rw [hinv] at h
  have h2 : y ^ 2 = 1 := by
    rw [pow_two]
    calc y * y = y * y⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel y
  have h3 : p ∣ 2 := hyo ▸ orderOf_dvd_of_pow_eq_one h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem le_centralizer_self_of_fixedPointFree {P : Subgroup G} {e : G} (he : e * e = 1)
    (heP : e ∈ Subgroup.normalizer (P : Set G))
    (hfix : P ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    P ≤ Subgroup.centralizer (P : Set G) := by
  have hab := isMulCommutative_of_conj_eq_inv fun x hx =>
    conj_eq_inv_of_inf_centralizer_eq_bot he heP hfix hx
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact congrArg Subtype.val (hab.is_comm.comm ⟨z, hz⟩ ⟨x, hx⟩)

omit [Finite G] in
theorem commutator_zpowers_eq_bot_iff' {t : G} {X : Subgroup G} :
    ⁅X, Subgroup.zpowers t⁆ = ⊥ ↔ ∀ x ∈ X, x * t = t * x := by
  rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]

theorem mem_qCoreOf_of_conj_eq_inv (h37 : S_G37) {M A' H : Subgroup G}
    (hSS : IsSStarIn M A') (hA' : CFSG.Open.IsElemAbelian 2 A') {a : G} (haA : a ∈ A')
    (ha1 : a ≠ 1) (hCH : Subgroup.centralizer ({a} : Set G) ≤ H) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {y : G} (hyP : y ∈ qCoreOf H p) (hyM : y ∈ M)
    (hinv : a * y * a⁻¹ = y⁻¹) : y ∈ qCoreOf M p := by
  have : Fact p.Prime := ⟨hp⟩
  have haM : a ∈ M := hSS.1 haA
  have haH : a ∈ H := hCH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  set D := qCoreOf H p ⊓ M with hDdef
  have hDp : IsPGroup p D := (qCoreOf_isPGroup H p).to_le inf_le_left
  have haD : a ∈ Subgroup.normalizer (D : Set G) :=
    mem_normalizer_inf (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) haH)
      (Subgroup.le_normalizer haM)
  set X := ⁅D, Subgroup.zpowers a⁆ with hXdef
  have hXD : X ≤ D := commutator_zpowers_le_of_mem_normalizer haD
  have hXC : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    intro c hc
    refine mem_normalizer_commutator (mem_normalizer_inf
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) (hCH hc.2))
      (Subgroup.le_normalizer hc.1)) ?_
    rw [← centralizer_zpowers_eq'] at hc
    exact Subgroup.centralizer_le_normalizer _ hc.2
  have hXa := G53.commutator_le_qCoreOf_of_isPGroup h37 hSS hA' haA ha1
    (hXD.trans inf_le_right) hXC hp hp2 (hDp.to_le hXD)
  have hyodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    obtain ⟨k, hk⟩ := hDp ⟨y, hyP, hyM⟩
    have hk' : y ^ p ^ k = 1 := congrArg Subtype.val hk
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2).pow (orderOf_dvd_of_pow_eq_one hk')
  have hinv' : ∀ x ∈ Subgroup.zpowers y, a * x * a⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hinv, inv_zpow]
  have hay : a ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (a * y * a⁻¹) = _
    rw [hinv, Subgroup.zpowers_inv]
  have hyy : ⁅Subgroup.zpowers y, Subgroup.zpowers a⁆ = Subgroup.zpowers y :=
    commutator_zpowers_eq_self_of_conj_eq_inv hay hinv' hyodd
  have hyD : Subgroup.zpowers y ≤ D := Subgroup.zpowers_le.mpr ⟨hyP, hyM⟩
  have hle : Subgroup.zpowers y ≤ ⁅X, Subgroup.zpowers a⁆ :=
    calc Subgroup.zpowers y = ⁅Subgroup.zpowers y, Subgroup.zpowers a⁆ := hyy.symm
      _ = ⁅⁅Subgroup.zpowers y, Subgroup.zpowers a⁆, Subgroup.zpowers a⁆ :=
          (congrArg (fun K => ⁅K, Subgroup.zpowers a⁆) hyy).symm
      _ ≤ ⁅X, Subgroup.zpowers a⁆ :=
          Subgroup.commutator_mono (Subgroup.commutator_mono hyD le_rfl) le_rfl
  exact hXa (hle (Subgroup.mem_zpowers y))

theorem zpowers_le_and_isSubnormal {K : Subgroup G} {w : G}
    (hw : w ∈ CFSG.fittingSubgroupOf K) :
    Subgroup.zpowers w ≤ generalizedFittingSubgroupOf K ∧
      ((Subgroup.zpowers w).subgroupOf (generalizedFittingSubgroupOf K)).IsSubnormal := by
  have hle : Subgroup.zpowers w ≤ CFSG.fittingSubgroupOf K := Subgroup.zpowers_le.mpr hw
  exact ⟨hle.trans le_sup_left, isSubnormal_subgroupOf_trans hle
    (isSubnormal_of_nilpotent (CFSG.fittingSubgroupOf_isNilpotent K) _ hle)
    (isSubnormal_subgroupOf_of_isNormalIn (fittingSubgroupOf_isNormalIn_generalizedFitting K))⟩

theorem isPGroup_of_pair (h37 : S_G37) {S : Sylow 2 G} {A : Subgroup G}
    (hG : GoldSetting G S A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a₁ a₂ : G} (ha₁A : a₁ ∈ A)
    (ha₂A : a₂ ∈ A) (ha₁1 : a₁ ≠ 1) (ha₂1 : a₂ ≠ 1) {H₁ H₂ : Subgroup G}
    (h₁ : Hyp54 p a₁ H₁) (h₂ : Hyp54 p a₂ H₂) (hAH₁ : A ≤ H₁) (hAH₂ : A ≤ H₂) {y : G}
    (hyP : y ∈ qCoreOf H₁ p) (hyo : orderOf y = p) (hyinv : a₁ * y * a₁⁻¹ = y⁻¹)
    (hya₂ : y * a₂ = a₂ * y) : IsPGroup p (generalizedFittingSubgroupOf H₁) := by
  have hsimple := hG.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have hsq : ∀ b ∈ A, b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact hG.elem.2 b hb
  have ha₁2 := hsq a₁ ha₁A
  have ha₂2 := hsq a₂ ha₂A
  have hcomm : a₁ * a₂ = a₂ * a₁ :=
    congrArg Subtype.val (hG.elem.1.is_comm.comm ⟨a₁, ha₁A⟩ ⟨a₂, ha₂A⟩)
  set P₁ := qCoreOf H₁ p with hP₁def
  set P₂ := qCoreOf H₂ p with hP₂def
  set Z₁ := P₁ ⊓ Subgroup.centralizer (P₁ : Set G) with hZ₁def
  set Z₂ := P₂ ⊓ Subgroup.centralizer (P₂ : Set G) with hZ₂def
  have hP₁p : IsPGroup p P₁ := qCoreOf_isPGroup H₁ p
  have hP₂p : IsPGroup p P₂ := qCoreOf_isPGroup H₂ p
  have hZ₁p : IsPGroup p Z₁ := hP₁p.to_le inf_le_left
  have hZ₂p : IsPGroup p Z₂ := hP₂p.to_le inf_le_left
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  have hyne : a₁ * y * a₁⁻¹ ≠ y := conj_ne_self_of_conj_eq_inv hp hp2 hyo hyinv
  have hN₁ : H₁ ≤ Subgroup.normalizer (P₁ : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H₁ p)
  have hN₂ : H₂ ≤ Subgroup.normalizer (P₂ : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H₂ p)
  have hZN₁ := le_normalizer_center H₁ p
  have hZN₂ := le_normalizer_center H₂ p
  have hconj : ∀ {e x : G}, x * e = e * x → e * x * e⁻¹ = x := fun h => by
    rw [← h, mul_inv_cancel_right]
  have hfpf : ∀ {P : Subgroup G} {e : G}, e * e = 1 → e ∈ Subgroup.normalizer (P : Set G) →
      P ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ → P ≤ P ⊓ Subgroup.centralizer (P : Set G) :=
    fun he heP hfix => le_inf le_rfl (le_centralizer_self_of_fixedPointFree he heP hfix)
  obtain ⟨g₁, hAg₁, hSS₁⟩ := hG.sstar H₁ h₁.coatom.1
  obtain ⟨g₂, hAg₂, hSS₂⟩ := hG.sstar H₂ h₂.coatom.1
  have hA₁' := isElemAbelian_conjSub_inf hG.elem g₁ H₁
  have hA₂' := isElemAbelian_conjSub_inf hG.elem g₂ H₂
  have hyH₂ : y ∈ H₂ := h₂.centralizer_le (Subgroup.mem_centralizer_singleton_iff.mpr hya₂)
  have hyP₂ : y ∈ P₂ := mem_qCoreOf_of_conj_eq_inv h37 hSS₂ hA₂'
    ⟨hAg₂ ⟨ha₁A, hAH₂ ha₁A⟩, hAH₂ ha₁A⟩ ha₁1 h₁.centralizer_le hp hp2 hyP hyH₂ hyinv
  have hyZ₂ : y ∈ Z₂ := h₂.cent ⟨hyP₂, Subgroup.mem_centralizer_singleton_iff.mpr hya₂⟩
  have hZa₂ : ∀ z ∈ Z₂, a₂ * z * a₂⁻¹ = z :=
    le_centralizer_of_isCyclic hp hp2 hZ₂p h₂.cyc ha₂2 (hZN₂ (hAH₂ ha₂A)) hyZ₂ hy1 (hconj hya₂)
  have hP₂a₂ : ¬ P₂ ≤ Z₂ := fun h => h₂.comm (commutator_zpowers_eq_bot_iff'.mpr fun x hx => by
    have h1 := hZa₂ x (h hx)
    calc x * a₂ = a₂ * x * a₂⁻¹ * a₂ := by rw [h1]
      _ = a₂ * x := by group)
  have hne : H₂ ≠ H₁ := by
    intro hH
    have hPP : P₂ = P₁ := by rw [hP₂def, hP₁def, hH]
    have hZZ : Z₂ = Z₁ := by rw [hZ₂def, hZ₁def, hPP]
    have hfix : P₁ ⊓ Subgroup.centralizer ({a₁} : Set G) = ⊥ := by
      by_contra hne'
      obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
      have hwZ : w ∈ Z₁ := h₁.cent hw
      have hZa₁ := le_centralizer_of_isCyclic hp hp2 hZ₁p h₁.cyc ha₁2 (hZN₁ (hAH₁ ha₁A)) hwZ
        (fun h => hw1 (Subtype.ext h)) (hconj (Subgroup.mem_centralizer_singleton_iff.mp hw.2))
      have hyZ₁ : y ∈ Z₁ := by
        rw [← hZZ]
        exact hyZ₂
      exact hyne (hZa₁ y hyZ₁)
    have hPZ : P₁ ≤ Z₁ := hfpf ha₁2 (hN₁ (hAH₁ ha₁A)) hfix
    exact hP₂a₂ (by rw [hPP, hZZ]; exact hPZ)
  have hNy : Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) = H₂ :=
    normalizer_zpowers_eq hsimple h₂ hyZ₂ hy1
  have hC21 : P₂ ⊓ Subgroup.centralizer ({a₁} : Set G) ≠ ⊥ := fun hfix =>
    hP₂a₂ (hfpf ha₁2 (hN₂ (hAH₂ ha₁A)) hfix)
  have hD : ⁅Subgroup.zpowers a₂, P₂ ⊓ Subgroup.centralizer ({a₁} : Set G)⁆ ≠ ⊥ := by
    intro h
    rw [commutator_zpowers_eq_bot_iff] at h
    have hle : P₂ ⊓ Subgroup.centralizer ({a₁} : Set G) ≤ Z₂ := fun x hx =>
      h₂.cent ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (h x hx)⟩
    have hyle := le_of_isCyclic_of_card_eq_prime hp h₂.cyc hZ₂p (Subgroup.zpowers_le.mpr hyZ₂)
      (by rw [Nat.card_zpowers, hyo]) hle hC21
    exact hyne (hconj (Subgroup.mem_centralizer_singleton_iff.mp
      (hyle (Subgroup.mem_zpowers y)).2))
  have ha₂D : a₂ ∈ Subgroup.normalizer
      ((P₂ ⊓ Subgroup.centralizer ({a₁} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf (hN₂ (hAH₂ ha₂A))
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm))
  obtain ⟨y₁, hy₁D, hy₁o, hy₁inv⟩ :=
    exists_orderOf_eq_conj_eq_inv hp (hP₂p.to_le inf_le_left) ha₂2 ha₂D hD
  have hy₁1 : y₁ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy₁o
    exact hp.one_lt.ne hy₁o
  have hy₁H₁ : y₁ ∈ H₁ := h₁.centralizer_le hy₁D.2
  have hy₁P₁ : y₁ ∈ P₁ := mem_qCoreOf_of_conj_eq_inv h37 hSS₁ hA₁'
    ⟨hAg₁ ⟨ha₂A, hAH₁ ha₂A⟩, hAH₁ ha₂A⟩ ha₂1 h₂.centralizer_le hp hp2 hy₁D.1 hy₁H₁ hy₁inv
  have hy₁Z₁ : y₁ ∈ Z₁ := h₁.cent ⟨hy₁P₁, hy₁D.2⟩
  have hNy₁ : Subgroup.normalizer ((Subgroup.zpowers y₁ : Subgroup G) : Set G) = H₁ :=
    normalizer_zpowers_eq hsimple h₁ hy₁Z₁ hy₁1
  obtain ⟨hyF₁, hysn₁⟩ := zpowers_le_and_isSubnormal (qCoreOf_le_fittingSubgroupOf H₁ p hp hyP)
  obtain ⟨hy₁F₂, hy₁sn₂⟩ :=
    zpowers_le_and_isSubnormal (qCoreOf_le_fittingSubgroupOf H₂ p hp hy₁D.1)
  have hπ : ¬ 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H₁)) := fun hπ =>
    hne (bender1970_1_7_iii_equalityOfMaximal hsimple H₁ h₁.coatom
      (subnormalHull H₁ (Subgroup.zpowers y)) (subnormalHull_le_generalizedFitting hyF₁)
      (isSubnormal_subnormalHull hyF₁ hysn₁)
      (generalizedFitting_inf_centralizer_subnormalHull_le H₁ _)
      ((subnormalHull_le_sup_centralizer hyF₁ hysn₁).trans
        ((sup_centralizer_le_normalizer _).trans hNy.le)) h₂.coatom (Or.inl hπ)
      ⟨subnormalHull H₂ (Subgroup.zpowers y₁),
        (subnormalHull_le_sup_centralizer hy₁F₂ hy₁sn₂).trans
          ((sup_centralizer_le_normalizer _).trans hNy₁.le),
        subnormalHull_le_generalizedFitting hy₁F₂, isSubnormal_subnormalHull hy₁F₂ hy₁sn₂,
        generalizedFitting_inf_centralizer_subnormalHull_le H₂ _⟩).symm
  have hP₁1 : P₁ ≠ ⊥ := fun h => h₁.comm (by rw [← hP₁def, h]; exact Subgroup.commutator_bot_left _)
  have hH₁1 : H₁ ≠ ⊥ := fun h => hP₁1 (le_bot_iff.mp (h ▸ qCoreOf_le H₁ p))
  have hπ1 : Nat.card (primesOfOrder (generalizedFittingSubgroupOf H₁)) = 1 :=
    le_antisymm (by omega)
      (one_le_card_primesOfOrder (generalizedFittingSubgroupOf_ne_bot hH₁1))
  obtain ⟨r, hr, hFr, -, -⟩ := exists_isPGroup_of_card_primesOfOrder_eq_one hπ1
  have hP₁F : P₁ ≤ generalizedFittingSubgroupOf H₁ :=
    (qCoreOf_le_fittingSubgroupOf H₁ p hp).trans le_sup_left
  rwa [eq_of_isPGroup_of_isPGroup hp hr hP₁p (hFr.to_le hP₁F) hP₁1]

end G54

open G53 G54 in
theorem G54_of (h28 : S_G28) (h37 : S_G37) : S_G54 := by
  intro G _ _ S A hG a haA ha1 H hH p hp hp2 hPa hCZ hZcyc
  have : Fact p.Prime := ⟨hp⟩
  have hHco : IsCoatom H := isCoatom_of_mem_benderM hH
  have hCH : Subgroup.centralizer ({a} : Set G) ≤ H := centralizer_le_of_mem_benderM hH
  have ha2 : a * a = 1 := by
    rw [← pow_two]
    exact hG.elem.2 a haA
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hG.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAH : A ≤ H := fun x hx =>
    hCH (Subgroup.mem_centralizer_singleton_iff.mpr (hcommA x hx a haA))
  have hAP : A ≤ Subgroup.normalizer (qCoreOf H p : Set G) :=
    hAH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p))
  have hPodd : Odd (Nat.card (qCoreOf H p)) := by
    obtain ⟨k, hk⟩ := (qCoreOf_isPGroup H p).exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨A₁, hA₁A, hA₁i, hA₁c⟩ := exists_hyperplane_commutator_ne_bot hG.elem haA ha1 hAP hPodd
    (by rwa [Subgroup.commutator_comm] at hPa)
  have haD : a ∈ Subgroup.normalizer
      ((qCoreOf H p ⊓ Subgroup.centralizer (A₁ : Set G) : Subgroup G) : Set G) := by
    refine mem_normalizer_inf (hAP haA) (Subgroup.le_normalizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcommA x (hA₁A hx) a haA
  obtain ⟨y, hyD, hyo, hyinv⟩ :=
    exists_orderOf_eq_conj_eq_inv hp ((qCoreOf_isPGroup H p).to_le inf_le_left) ha2 haD hA₁c
  obtain ⟨n, hnN, hnA₁⟩ := h28 G A (Subgroup.normalizer (A : Set G)) A₁ hG.elem
    (four_le_card_of_goldSetting hG) le_rfl hG.irreducible hA₁A hA₁i a haA ha1
  have hn' : n⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hnN
  have ha₂A : n⁻¹ * a * n ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp hn' a).mp haA
    rwa [inv_inv] at this
  have ha₂1 : n⁻¹ * a * n ≠ 1 := fun h => ha1 (by
    calc a = n * (n⁻¹ * a * n) * n⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have h₂ : Hyp54 p (n⁻¹ * a * n) (H.map (MulAut.conj n⁻¹).toMonoidHom) := by
    have := (Hyp54.mk hHco hCH hPa hCZ hZcyc).conj n⁻¹
    rwa [inv_inv] at this
  have hAH₂ : A ≤ H.map (MulAut.conj n⁻¹).toMonoidHom := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hn']
    exact Subgroup.map_mono hAH
  exact isPGroup_of_pair h37 hG hp hp2 haA ha₂A ha1 ha₂1 ⟨hHco, hCH, hPa, hCZ, hZcyc⟩ h₂ hAH hAH₂
    hyD.1 hyo hyinv ((Subgroup.mem_centralizer_iff.mp hyD.2) _ hnA₁).symm

end CFSG.Goldschmidt

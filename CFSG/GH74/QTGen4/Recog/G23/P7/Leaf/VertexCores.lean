module

public import CFSG.GH74.QTGen4.Recog.G23.P7.LeafWrappers
public import CFSG.Milestones.LR_Brauer_Suzuki_central_involution
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.Quasithin.EmptyFaithful.S143VQ8
public import CFSG.GH74.QTGen4.Recog.G23.HK2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem vc_sl3_invol : ∀ A : SL(2, ZMod 3), A * A = 1 → A ≠ 1 → A = -1 := by decide

theorem vc_sl3_pow8 : ∀ A : SL(2, ZMod 3), A ^ 8 = 1 → A ^ 4 = 1 := by decide

theorem vc_sl3_normal_odd : ∀ x : SL(2, ZMod 3), x ^ 3 = 1 → x ≠ 1 →
    ∃ g : SL(2, ZMod 3), g * x * g⁻¹ ≠ x ∧ g * x * g⁻¹ ≠ x * x := by decide

theorem vc_q8_central : ∀ x : QuaternionGroup 2, (∀ y : QuaternionGroup 2, x * y = y * x) →
    x = 1 ∨ x = QuaternionGroup.a 2 := by decide

theorem vc_q8_invol : ∀ x : QuaternionGroup 2, x * x = 1 → x ≠ 1 → x = QuaternionGroup.a 2 := by
  decide

theorem vc_card_sl3 : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Matrix.card_SL_field 2]
  simp [ZMod.card, Fin.prod_univ_two]

theorem vc_comm_zpow {σ l : G} (hc : σ * l = l * σ) {s : G} (hs : s ∈ Subgroup.zpowers σ) :
    s * l = l * s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  exact (Commute.zpow_left (show Commute σ l from hc) k).eq

theorem vc_mem_sup_decomp {σ : G} {L : Subgroup G} (hc : ∀ l ∈ L, σ * l = l * σ) {x : G}
    (hx : x ∈ Subgroup.zpowers σ ⊔ L) : ∃ s ∈ Subgroup.zpowers σ, ∃ l ∈ L, x = s * l := by
  let D : Subgroup G :=
    { carrier := {x | ∃ s ∈ Subgroup.zpowers σ, ∃ l ∈ L, x = s * l}
      mul_mem' := by
        rintro _ _ ⟨s₁, hs₁, l₁, hl₁, rfl⟩ ⟨s₂, hs₂, l₂, hl₂, rfl⟩
        refine ⟨s₁ * s₂, Subgroup.mul_mem _ hs₁ hs₂, l₁ * l₂, L.mul_mem hl₁ hl₂, ?_⟩
        calc s₁ * l₁ * (s₂ * l₂) = s₁ * (l₁ * s₂) * l₂ := by group
          _ = s₁ * (s₂ * l₁) * l₂ := by rw [vc_comm_zpow (hc l₁ hl₁) hs₂]
          _ = s₁ * s₂ * (l₁ * l₂) := by group
      one_mem' := ⟨1, Subgroup.one_mem _, 1, L.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨s, hs, l, hl, rfl⟩
        refine ⟨s⁻¹, Subgroup.inv_mem _ hs, l⁻¹, L.inv_mem hl, ?_⟩
        have hcm : Commute s l := vc_comm_zpow (hc l hl) hs
        calc (s * l)⁻¹ = l⁻¹ * s⁻¹ := by group
          _ = s⁻¹ * l⁻¹ := hcm.inv_inv.eq.symm }
  have hle : Subgroup.zpowers σ ⊔ L ≤ D := sup_le
    (fun s hs => show s ∈ D from ⟨s, hs, 1, L.one_mem, (mul_one s).symm⟩)
    (fun l hl => show l ∈ D from ⟨1, Subgroup.one_mem _, l, hl, (one_mul l).symm⟩)
  obtain ⟨s, hs, l, hl, hxs⟩ : ∃ s ∈ Subgroup.zpowers σ, ∃ l ∈ L, x = s * l := hle hx
  exact ⟨s, hs, l, hl, hxs⟩

theorem vc_zpow_mod3 {x : G} (h3 : x ^ 3 = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x ∨ x ^ k = x * x := by
  have h3z : x ^ (3 : ℤ) = 1 := by exact_mod_cast h3
  have hk : x ^ k = x ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, h3z, one_zpow, mul_one]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · left; rw [hk, h, zpow_zero]
  · right; left; rw [hk, h, zpow_one]
  · right; right; rw [hk, h, zpow_two]

theorem vc_zpow_three {σ : G} (h3 : σ ^ 3 = 1) {x : G} (hx : x ∈ Subgroup.zpowers σ) :
    x = 1 ∨ x = σ ∨ x = σ⁻¹ := by
  have hσσ : σ * σ = σ⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact h3)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases vc_zpow_mod3 h3 k with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.trans hσσ))

theorem vc_card_L {L : Subgroup G} (eL : ↥L ≃* SL(2, ZMod 3)) : Nat.card ↥L = 24 := by
  rw [← vc_card_sl3, Nat.card_congr eL.toEquiv]

theorem vc_invol_unique {L : Subgroup G} (eL : ↥L ≃* SL(2, ZMod 3)) {z : G} (hzL : z ∈ L)
    (hz1 : z ≠ 1) (hz2 : z * z = 1) {u : G} (huL : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    u = z := by
  have hu' : (⟨u, huL⟩ : ↥L) * ⟨u, huL⟩ = 1 := Subtype.ext hu2
  have hu1' : (⟨u, huL⟩ : ↥L) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hz' : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 := Subtype.ext hz2
  have hz1' : (⟨z, hzL⟩ : ↥L) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have e1 : eL ⟨u, huL⟩ = -1 :=
    vc_sl3_invol _ (by rw [← map_mul, hu', map_one])
      (fun h => hu1' (eL.injective (h.trans (map_one eL).symm)))
  have e2 : eL ⟨z, hzL⟩ = -1 :=
    vc_sl3_invol _ (by rw [← map_mul, hz', map_one])
      (fun h => hz1' (eL.injective (h.trans (map_one eL).symm)))
  have : (⟨u, huL⟩ : ↥L) = ⟨z, hzL⟩ := eL.injective (e1.trans e2.symm)
  exact congrArg Subtype.val this

theorem vc_pow8 {L : Subgroup G} (eL : ↥L ≃* SL(2, ZMod 3)) {x : G} (hx : x ∈ L)
    (h8 : x ^ 8 = 1) : x ^ 4 = 1 := by
  have h : (⟨x, hx⟩ : ↥L) ^ 8 = 1 := Subtype.ext (by simpa using h8)
  have h' : (⟨x, hx⟩ : ↥L) ^ 4 = 1 := by
    apply eL.injective
    rw [map_pow, map_one]
    exact vc_sl3_pow8 _ (by rw [← map_pow, h, map_one])
  simpa using congrArg Subtype.val h'

theorem vc_normal_odd [Finite G] {L : Subgroup G} (eL : ↥L ≃* SL(2, ZMod 3)) (N : Subgroup ↥L)
    (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hcardL : Nat.card ↥L = 24 := vc_card_L eL
  by_contra hne
  obtain ⟨y, hyN, hy1⟩ : ∃ y ∈ N, y ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ y ∈ N, y = 1 := fun y hy => by
      by_contra h
      exact hcon ⟨y, hy, h⟩
    exact hne ((Subgroup.eq_bot_iff_forall N).mpr hcon')
  have hc2 : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hodd
  have hc8 : Nat.Coprime (Nat.card N) 8 := by
    have := (Nat.Coprime.pow_left 3 hc2).symm
    norm_num at this
    exact this
  have hdvd : Nat.card N ∣ 3 := by
    have h24 : Nat.card N ∣ 8 * 3 := by
      have := Subgroup.card_subgroup_dvd_card N
      rw [hcardL] at this
      exact this
    exact Nat.Coprime.dvd_of_dvd_mul_left hc8 h24
  have hyord : orderOf y = 3 := by
    have h1 : orderOf y ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨y, hyN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp (h1.trans hdvd) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have hzp_le : Subgroup.zpowers y ≤ N := Subgroup.zpowers_le.mpr hyN
  have hcardz : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyord]
  have hcardN : Nat.card N = 3 := by
    have h1 : 3 ≤ Nat.card N := by
      have := Subgroup.card_le_of_le hzp_le
      omega
    have h2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hzN : Subgroup.zpowers y = N :=
    Subgroup.eq_of_le_of_card_ge hzp_le (by rw [hcardN, hcardz])
  have hy3 : y ^ 3 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hw3 : eL y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hw1 : eL y ≠ 1 := fun h => hy1 (eL.injective (h.trans (map_one eL).symm))
  obtain ⟨g', hg1, hg2⟩ := vc_sl3_normal_odd (eL y) hw3 hw1
  set g : ↥L := eL.symm g' with hgdef
  have hu : g * y * g⁻¹ ∈ Subgroup.zpowers y := by
    rw [hzN]; exact hN.conj_mem y hyN g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
  have heu : eL (g * y * g⁻¹) = g' * eL y * g'⁻¹ := by
    rw [map_mul, map_mul, map_inv, hgdef, MulEquiv.apply_symm_apply]
  have hu1 : g * y * g⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [h] at this
    simpa using this
  have hwk : eL (g * y * g⁻¹) = eL y ^ k := by rw [← hk, map_zpow]
  rcases vc_zpow_mod3 hw3 k with h | h | h
  · apply hu1
    apply eL.injective
    rw [map_one, hwk, h]
  · apply hg1
    rw [← heu, hwk, h]
  · apply hg2
    rw [← heu, hwk, h]


theorem vc_odd_card_oddCore (K : Type) [Group K] [Finite K] :
    Odd (Nat.card (CFSG.oddCore K)) := by
  have hle : CFSG.oddCore K ≤ CFSG.pPrimeCore 2 K :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have hdvd : Nat.card (CFSG.oddCore K) ∣ Nat.card (CFSG.pPrimeCore 2 K) :=
    Subgroup.card_dvd_of_le hle
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2) (G := K)))

def vcConj {C : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (C : Set G)) : ↥C ≃* ↥C where
  toFun c := ⟨g * c * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (c : G)).mp c.2⟩
  invFun c := ⟨g⁻¹ * c * g⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) (c : G)).mp c.2⟩
  left_inv c := Subtype.ext (by simp [mul_assoc])
  right_inv c := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem vc_oddCore_map_le [Finite G] {C : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) :
    (CFSG.oddCore ↥C).map (vcConj hg).toMonoidHom ≤ CFSG.oddCore ↥C := by
  haveI : (CFSG.oddCore ↥C).Normal := inferInstance
  have hN : ((CFSG.oddCore ↥C).map (vcConj hg).toMonoidHom).Normal :=
    Subgroup.Normal.map this _ (vcConj hg).surjective
  have hodd : Odd (Nat.card ((CFSG.oddCore ↥C).map (vcConj hg).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (vcConj hg).injective]
    exact vc_odd_card_oddCore ↥C
  exact le_sSup ⟨hN, hodd⟩

theorem vc_zOf_mem_inf {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hl : HLetters H H₁ H₂ e) :
    zOf e ∈ H₁ ⊓ H₂ := by
  have hr : FreeGroup.lift e (FreeGroup.mk ([(0, true), (1, true), (0, true), (1, true),
      (3, false), (2, false), (3, false), (2, false)] : List (Fin 6 × Bool))) = 1 :=
    hl.rels _ (by simp [g23WordsH])
  have hr' : e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹ = 1 := by
    simpa [FreeGroup.lift_mk, mul_assoc] using hr
  have hA : e 0 * e 1 * e 0 * e 1 = e 2 * e 3 * e 2 * e 3 := by
    calc e 0 * e 1 * e 0 * e 1
        = (e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹) *
            (e 2 * e 3 * e 2 * e 3) := by group
      _ = e 2 * e 3 * e 2 * e 3 := by rw [hr', one_mul]
  have hz2 : zOf e = (e 2 * e 3) ^ 2 := by
    unfold zOf
    simp only [sq, mul_assoc] at hA ⊢
    exact hA
  have he0 : e 0 ∈ H₁ := by
    rw [← hl.gen₁]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he1 : e 1 ∈ H₁ := by
    rw [← hl.gen₁]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have he2 : e 2 ∈ H₂ := by
    rw [← hl.gen₂]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he3 : e 3 ∈ H₂ := by
    rw [← hl.gen₂]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact pow_mem (mul_mem he0 he1) 2
  · rw [hz2]; exact pow_mem (mul_mem he2 he3) 2

theorem vc_ne_one [Finite G] {H L : Subgroup G} {σ : G}
    (hcent : Subgroup.centralizer ({σ} : Set G) ⊓ H = Subgroup.zpowers σ ⊔ L)
    (hcardH : 24 < Nat.card H) (hcardL : Nat.card L = 24) : σ ≠ 1 := by
  rintro rfl
  have hHL : H ≤ L := by
    intro x hx
    have hc1 : x ∈ Subgroup.centralizer ({1} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (by rw [mul_one, one_mul])
    have hx' : x ∈ Subgroup.centralizer ({1} : Set G) ⊓ H := Subgroup.mem_inf.mpr ⟨hc1, hx⟩
    rw [hcent, Subgroup.zpowers_one_eq_bot, bot_sup_eq] at hx'
    exact hx'
  have := Subgroup.card_le_of_le hHL
  omega


theorem vc_vertexCore [Finite G] [G23Leaf LeafSylow2Cent] {H L : Subgroup G} {e : Fin 6 → G}
    {σ : G}
    (eL : ↥L ≃* SL(2, ZMod 3))
    (hzL : zOf e ∈ L) (hz1 : zOf e ≠ 1) (hz2 : zOf e * zOf e = 1)
    (hCz : Subgroup.centralizer ({zOf e} : Set G) = H)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hcentσ : Subgroup.centralizer ({σ} : Set G) ⊓ H = Subgroup.zpowers σ ⊔ L)
    (hdisj : Subgroup.zpowers σ ⊓ L = ⊥)
    (ht : e 4 ∈ H) (ht2 : e 4 * e 4 = 1) (ht1 : e 4 ≠ 1) (hte : e 4 ≠ zOf e)
    (htσ : e 4 * σ * e 4 = σ⁻¹)
    (hconj : ∃ g ∈ L ⊔ Subgroup.zpowers (e 4), g * e 4 * g⁻¹ = e 4 * zOf e)
    (hodd : ∀ S : Subgroup G, S ≤ H → Odd (Nat.card S) → Nat.card S ∣ 9)
    (hOC : ∀ x : G, orderOf x = 2 → IsConj (zOf e) x) :
    ∃ M : Subgroup G, VertexCore e H σ L M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardL : Nat.card ↥L = 24 := vc_card_L eL
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hinv : ∀ u ∈ L, u * u = 1 → u ≠ 1 → u = zOf e :=
    fun u hu h2 h1 => vc_invol_unique eL hzL hz1 hz2 hu h2 h1
  have hz_ord : orderOf (zOf e) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  set C : Subgroup G := Subgroup.centralizer ({σ} : Set G) with hCdef
  have hzH : zOf e ∈ H := by
    rw [← hCz]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcommH : ∀ h ∈ H, h * zOf e = zOf e * h := fun h hh => by
    rw [← hCz] at hh; exact Subgroup.mem_centralizer_singleton_iff.mp hh
  have hsup_iff : ∀ x, x ∈ C ⊓ H ↔ x ∈ Subgroup.zpowers σ ⊔ L := fun x => by rw [hcentσ]
  have hσC : σ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hLcent : ∀ l ∈ L, σ * l = l * σ := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp ((hsup_iff l).mpr (Subgroup.mem_sup_right hl))).1).symm
  have hLC : L ≤ C := fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hLcent l hl).symm
  have hLH : L ≤ H := fun l hl => (Subgroup.mem_inf.mp ((hsup_iff l).mpr (Subgroup.mem_sup_right hl))).2
  have hzpowH : Subgroup.zpowers σ ≤ H := fun s hs =>
    (Subgroup.mem_inf.mp ((hsup_iff s).mpr (Subgroup.mem_sup_left hs))).2
  have hdec : ∀ x ∈ C ⊓ H, ∃ s ∈ Subgroup.zpowers σ, ∃ l ∈ L, x = s * l := fun x hx =>
    vc_mem_sup_decomp hLcent ((hsup_iff x).mp hx)
  have hσ3' : ∀ s ∈ Subgroup.zpowers σ, s ^ 3 = 1 := fun s hs => by
    rcases vc_zpow_three hσ3 hs with h | h | h
    · rw [h, one_pow]
    · rw [h, hσ3]
    · rw [h, inv_pow, hσ3, inv_one]
  have hinv4 : (e 4)⁻¹ = e 4 := inv_eq_of_mul_eq_one_right ht2
  have htz : e 4 * zOf e = zOf e * e 4 := hcommH (e 4) ht
  have hσ' : σ = e 4 * σ⁻¹ * e 4 := by
    calc σ = (σ⁻¹)⁻¹ := (inv_inv σ).symm
      _ = (e 4 * σ * e 4)⁻¹ := by rw [htσ]
      _ = e 4 * σ⁻¹ * e 4 := by rw [mul_inv_rev, mul_inv_rev, hinv4, mul_assoc]
  have hσne_inv : σ⁻¹ ≠ σ := by
    intro h
    apply hσ1
    have h' : σ * σ⁻¹ = σ * σ := congrArg (fun y => σ * y) h
    rw [mul_inv_cancel] at h'
    calc σ = σ * σ * σ := by rw [← h', one_mul]
      _ = 1 := by rw [← pow_three']; exact hσ3
  have htC : ∀ c ∈ C, e 4 * c * (e 4)⁻¹ ∈ C := by
    intro c hc
    have hcσ : Commute c σ := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcσ' : c * σ⁻¹ = σ⁻¹ * c := hcσ.inv_right.eq
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff, hinv4]
    calc e 4 * c * e 4 * σ = e 4 * c * e 4 * (e 4 * σ⁻¹ * e 4) := by rw [← hσ']
      _ = e 4 * c * (e 4 * e 4) * σ⁻¹ * e 4 := by group
      _ = e 4 * c * σ⁻¹ * e 4 := by rw [ht2, mul_one]
      _ = e 4 * (c * σ⁻¹) * e 4 := by group
      _ = e 4 * (σ⁻¹ * c) * e 4 := by rw [hcσ']
      _ = e 4 * σ⁻¹ * (e 4 * e 4) * c * e 4 := by rw [ht2]; group
      _ = (e 4 * σ⁻¹ * e 4) * (e 4 * c * e 4) := by group
      _ = σ * (e 4 * c * e 4) := by rw [← hσ']
  have htN : e 4 ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact htC x hx
    · intro hx
      have h := htC _ hx
      have e1 : e 4 * (e 4 * x * (e 4)⁻¹) * (e 4)⁻¹ = x := by
        rw [hinv4]
        calc e 4 * (e 4 * x * e 4) * e 4 = (e 4 * e 4) * x * (e 4 * e 4) := by group
          _ = x := by rw [ht2, one_mul, mul_one]
      rwa [e1] at h
  have hLN : L ⊔ Subgroup.zpowers (e 4) ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (fun l hl => Subgroup.le_normalizer (hLC hl)) (Subgroup.zpowers_le.mpr htN)
  set M : Subgroup G := (CFSG.oddCore ↥C).map C.subtype with hMdef
  have hMC : M ≤ C := Subgroup.map_subtype_le (CFSG.oddCore ↥C)
  have hMchar : ∀ g ∈ Subgroup.normalizer (C : Set G), ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hg m hm
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hm
    exact Subgroup.mem_map.mpr ⟨vcConj hg x, vc_oddCore_map_le hg ⟨x, hx, rfl⟩, rfl⟩
  have hMnormC : ∀ c ∈ C, ∀ m ∈ M, c * m * c⁻¹ ∈ M := fun c hc m hm =>
    hMchar c (Subgroup.le_normalizer hc) m hm
  have hMnormN : ∀ g ∈ Subgroup.normalizer (C : Set G), g ∈ Subgroup.normalizer (M : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hMchar g hg x hx
    · intro hx
      have h := hMchar g⁻¹ (Subgroup.inv_mem _ hg) _ hx
      have e1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e1] at h
  have hM_odd : Odd (Nat.card M) := by
    rw [hMdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact vc_odd_card_oddCore ↥C
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Subgroup ↥L, Nat.card P₀ = 2 ^ 3 :=
    Sylow.exists_subgroup_card_pow_prime 2 (by rw [hcardL]; norm_num)
  obtain ⟨Q₀, hQ0def⟩ : ∃ Q₀ : Subgroup G, Q₀ = P₀.map L.subtype := ⟨_, rfl⟩
  have hQ0L : Q₀ ≤ L := by rw [hQ0def]; exact Subgroup.map_subtype_le P₀
  have hQ0card : Nat.card Q₀ = 8 := by
    rw [hQ0def, Subgroup.card_map_of_injective L.subtype_injective, hP₀]; norm_num
  have hQ0two : IsPGroup 2 Q₀ := by
    rw [hQ0def]; exact IsPGroup.map (IsPGroup.iff_card.mpr ⟨3, hP₀⟩) L.subtype
  have hQ0H : Q₀ ≤ H := hQ0L.trans hLH
  have hQ0C : Q₀ ≤ C := hQ0L.trans hLC
  have hcommQ0 : ∀ q ∈ Q₀, q * zOf e = zOf e * q := fun q hq => hcommH q (hQ0H hq)
  have hzQ0 : zOf e ∈ Q₀ := by
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q₀) 2 (by rw [hQ0card]; norm_num)
    have hu2 : (u : G) * u = 1 := by
      have h := congrArg Subtype.val (pow_orderOf_eq_one u)
      rw [hu] at h
      simpa [pow_two] using h
    have hu1 : (u : G) ≠ 1 := by
      intro h
      have hu' : u = 1 := Subtype.ext h
      rw [hu', orderOf_one] at hu
      norm_num at hu
    have := hinv (u : G) (hQ0L u.2) hu2 hu1
    rw [← this]
    exact u.2
  obtain ⟨zQ, hzQ⟩ : ∃ zQ : ↥Q₀, (zQ : G) = zOf e := ⟨⟨zOf e, hzQ0⟩, rfl⟩
  have hzQ1 : zQ ≠ 1 := fun h => hz1 (by rw [← hzQ, h]; rfl)
  have hzQ2 : zQ * zQ = 1 := Subtype.ext (by simp [hzQ, hz2])
  have hsqQ : ∀ a : ↥Q₀, a ≠ 1 → a ≠ zQ → a ^ 2 = zQ := by
    intro a ha1 haz
    have ha_L : (a : G) ∈ L := hQ0L a.2
    have ha8 : (a : G) ^ 8 = 1 := by
      have h := pow_card_eq_one' (G := ↥Q₀) (x := a)
      rw [hQ0card] at h
      simpa using congrArg Subtype.val h
    have ha4 : (a : G) ^ 4 = 1 := vc_pow8 eL ha_L ha8
    have hb : (a : G) ^ 2 * (a : G) ^ 2 = 1 := by rw [← pow_add]; exact ha4
    by_cases hb1 : (a : G) ^ 2 = 1
    · exfalso
      apply haz
      apply Subtype.ext
      rw [hzQ]
      have hna1 : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
      have hsq1 : (a : G) * (a : G) = 1 := by rw [← pow_two]; exact hb1
      exact hinv _ ha_L hsq1 hna1
    · apply Subtype.ext
      rw [hzQ, Subgroup.coe_pow]
      exact hinv _ (L.pow_mem ha_L 2) hb hb1
  have hQ8 : Nonempty (↥Q₀ ≃* QuaternionGroup 2) :=
    CFSG.Quasithin.S143V.nonempty_mulEquiv_quaternion hQ0card hzQ1
      (fun a => Subtype.ext (by simpa [hzQ] using hcommQ0 a a.2)) hsqQ
  have hcenter : ∀ q ∈ Q₀, (∀ q' ∈ Q₀, q * q' = q' * q) ↔ q ∈ Subgroup.zpowers (zOf e) := by
    intro q hq
    constructor
    · intro hc
      obtain ⟨ψ⟩ := hQ8
      have hcen : ∀ y : QuaternionGroup 2, ψ ⟨q, hq⟩ * y = y * ψ ⟨q, hq⟩ := by
        intro y
        have hx : (⟨q, hq⟩ : ↥Q₀) * ψ.symm y = ψ.symm y * ⟨q, hq⟩ :=
          Subtype.ext (hc _ (ψ.symm y).2)
        have := congrArg ψ hx
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
      have hψz : ψ zQ = QuaternionGroup.a 2 := by
        apply vc_q8_invol
        · rw [← map_mul, hzQ2, map_one]
        · intro h; exact hzQ1 (ψ.injective (h.trans (map_one ψ).symm))
      rcases vc_q8_central _ hcen with h1 | h1
      · have h2 : (⟨q, hq⟩ : ↥Q₀) = 1 := ψ.injective (h1.trans (map_one ψ).symm)
        have hq1 : q = 1 := congrArg Subtype.val h2
        rw [hq1]; exact Subgroup.one_mem _
      · have h2 : (⟨q, hq⟩ : ↥Q₀) = zQ := ψ.injective (h1.trans hψz.symm)
        have hq1 : q = zOf e := by rw [← hzQ]; exact congrArg Subtype.val h2
        rw [hq1]; exact Subgroup.mem_zpowers _
    · intro hq'
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hq'
      intro q' hq'Q
      have hcm : Commute (zOf e) q' := (hcommQ0 q' hq'Q).symm
      rw [← hk]
      exact (hcm.zpow_left k).eq
  have hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ C ⊓ Subgroup.centralizer ({zOf e} : Set G) →
      Q₀ ≤ R → R = Q₀ := by
    intro R hR hRC hQR
    have hRL : R ≤ L := by
      intro r hr
      have hrC := Subgroup.mem_inf.mp (hRC hr)
      have hrH : r ∈ H := by rw [← hCz]; exact hrC.2
      obtain ⟨s, hs, l, hl, hrsl⟩ := hdec r (Subgroup.mem_inf.mpr ⟨hrC.1, hrH⟩)
      obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
      have hrn : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hcom : Commute s l := vc_comm_zpow (hLcent l hl) hs
      rw [hrsl, hcom.mul_pow] at hrn
      have hsn : s ^ 2 ^ n = (l ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hrn
      have hsnL : s ^ 2 ^ n ∈ L := by rw [hsn]; exact L.inv_mem (L.pow_mem hl _)
      have hsnS : s ^ 2 ^ n ∈ Subgroup.zpowers σ := Subgroup.pow_mem _ hs _
      have hs1 : s ^ 2 ^ n = 1 := by
        have : s ^ 2 ^ n ∈ Subgroup.zpowers σ ⊓ L := Subgroup.mem_inf.mpr ⟨hsnS, hsnL⟩
        rw [hdisj, Subgroup.mem_bot] at this
        exact this
      have hcop : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
      have hs_eq : s = 1 := by
        have h := (pow_gcd_eq_one (a := s) (m := 2 ^ n) (n := 3)).mpr ⟨hs1, hσ3' s hs⟩
        rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
        exact h
      rw [hrsl, hs_eq, one_mul]
      exact hl
    have hRcard : Nat.card R ∣ 24 := by rw [← hcardL]; exact Subgroup.card_dvd_of_le hRL
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
    have hm3 : m ≤ 3 := by
      by_contra hc
      have hc' : 4 ≤ m := by omega
      have h16 : 2 ^ 4 ∣ 2 ^ m := pow_dvd_pow 2 hc'
      rw [← hm] at h16
      have := dvd_trans h16 hRcard
      norm_num at this
    have hle8 : Nat.card R ≤ 8 := by
      rw [hm]
      calc 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hm3
        _ = 8 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge hQR (by rw [hQ0card]; exact hle8)).symm
  have hQ0Cs : IsPGroup 2 (Q₀.subgroupOf C) :=
    hQ0two.of_equiv (Subgroup.subgroupOfEquivOfLe hQ0C).symm
  obtain ⟨P, hQP⟩ := IsPGroup.exists_le_sylow hQ0Cs
  have hzC : zOf e ∈ C := hLC hzL
  obtain ⟨zC, hzC'⟩ : ∃ zC : ↥C, (zC : G) = zOf e := ⟨⟨zOf e, hzC⟩, rfl⟩
  have hPeq : (P : Subgroup ↥C) = Q₀.subgroupOf C := by
    have hR'two : IsPGroup 2 ((P : Subgroup ↥C).map C.subtype) := P.isPGroup'.map C.subtype
    have hR'C : (P : Subgroup ↥C).map C.subtype ≤ C := Subgroup.map_subtype_le (P : Subgroup ↥C)
    have hQR' : Q₀ ≤ (P : Subgroup ↥C).map C.subtype := by
      intro q hq
      have hqC : q ∈ C := hQ0C hq
      exact Subgroup.mem_map.mpr ⟨⟨q, hqC⟩, hQP (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
    have hRQ : (P : Subgroup ↥C).map C.subtype = Q₀ :=
      maximal_two_of_cent hz_ord hzC hQ0C hQ0two hzQ0 hcenter hmax _ hR'two hR'C hQR'
    have hcardP : Nat.card (P : Subgroup ↥C) = 8 := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective, hRQ, hQ0card]
    exact (Subgroup.eq_of_le_of_card_ge hQP (le_of_eq (by
      rw [hcardP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0C).toEquiv, hQ0card]))).symm
  have hquatP : Nonempty (↥(P : Subgroup ↥C) ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    rw [hPeq]
    obtain ⟨ψ⟩ := hQ8
    exact ⟨(Subgroup.subgroupOfEquivOfLe hQ0C).trans ψ⟩
  have hz'P : zC ∈ (P : Subgroup ↥C) := by
    rw [hPeq, Subgroup.mem_subgroupOf, hzC']; exact hzQ0
  have hzC_ord : orderOf zC = 2 := by
    rw [← Subgroup.orderOf_coe, hzC', hz_ord]
  have hBS := CFSG.Milestones.brauer_suzuki 3 le_rfl P hquatP zC hz'P hzC_ord
  have hzz : zC * zC = 1 := Subtype.ext (by simp [hzC', hz2])
  have hfrat := CFSG.Adapters.eq_centralizer_mul_oddCore hzz hBS
  have hzpowM : Subgroup.zpowers σ ≤ M := by
    set σC : ↥C := ⟨σ, hσC⟩ with hσCdef
    have hcen : ∀ g : ↥C, g * σC = σC * g := fun g =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    have hNσ : (Subgroup.zpowers σC).Normal := ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hc : g * σC ^ k = σC ^ k * g := (Commute.zpow_right (show Commute g σC from hcen g) k).eq
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers σC) k⟩
    have hodd' : Odd (Nat.card (Subgroup.zpowers σC)) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk σ hσC, hord]
      exact ⟨1, by norm_num⟩
    have hle : Subgroup.zpowers σC ≤ CFSG.oddCore ↥C := le_sSup ⟨hNσ, hodd'⟩
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.mem_map.mpr ⟨σC ^ k, hle (Subgroup.zpow_mem _ (Subgroup.mem_zpowers σC) k), rfl⟩
  have hM_union : M ⊔ L = C := by
    apply le_antisymm (sup_le hMC hLC)
    intro g hg
    obtain ⟨c, hc, k, hk, hgck⟩ := hfrat ⟨g, hg⟩
    have hcz : (c : G) * zOf e = zOf e * (c : G) := by
      have h := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
      simpa [hzC'] using h
    have hcH : (c : G) ∈ H := by
      rw [← hCz]; exact Subgroup.mem_centralizer_singleton_iff.mpr hcz
    obtain ⟨s, hs, l, hl, hcsl⟩ := hdec (c : G) (Subgroup.mem_inf.mpr ⟨c.2, hcH⟩)
    have hgG : g = (c : G) * (k : G) := by
      have h := congrArg Subtype.val hgck
      simpa using h
    have hkM : (k : G) ∈ M := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    rw [hgG, hcsl]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (hzpowM hs)) (Subgroup.mem_sup_right hl))
      (Subgroup.mem_sup_left hkM)
  have hM_inf_L : M ⊓ L = ⊥ := by
    have hNn : (M.subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hMnormC (g : G) (hLC g.2) _ hn⟩
    have hNodd : Odd (Nat.card (M.subgroupOf L)) := by
      have h1 : Nat.card (M.subgroupOf L) = Nat.card ((M.subgroupOf L).map L.subtype) :=
        (Subgroup.card_map_of_injective L.subtype_injective).symm
      have h2 : (M.subgroupOf L).map L.subtype ≤ M := by
        rintro _ ⟨n, hn, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hn
      rw [h1]
      exact Odd.of_dvd_nat hM_odd (Subgroup.card_dvd_of_le h2)
    have hbot := vc_normal_odd eL (M.subgroupOf L) hNn hNodd
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxM, hxL⟩ := Subgroup.mem_inf.mp hx
    have hmem : (⟨x, hxL⟩ : ↥L) ∈ M.subgroupOf L := Subgroup.mem_subgroupOf.mpr hxM
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  have hMH : M ⊓ H = Subgroup.zpowers σ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxM, hxH⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨s, hs, l, hl, hxsl⟩ := hdec x (Subgroup.mem_inf.mpr ⟨hMC hxM, hxH⟩)
      have hsM := hzpowM hs
      have hlM : l ∈ M := by
        have := M.mul_mem (M.inv_mem hsM) hxM
        rw [hxsl, ← mul_assoc, inv_mul_cancel, one_mul] at this
        exact this
      have hl1 : l = 1 := by
        have : l ∈ M ⊓ L := Subgroup.mem_inf.mpr ⟨hlM, hl⟩
        rw [hM_inf_L, Subgroup.mem_bot] at this
        exact this
      rw [hxsl, hl1, mul_one]
      exact hs
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hzpowM hx, hzpowH hx⟩


  have hkey : ∀ d ∈ C, ∀ y ∈ Subgroup.zpowers σ, d * y * d⁻¹ = y := fun d hd y hy => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hdσ : Commute d σ := Subgroup.mem_centralizer_singleton_iff.mp hd
    rw [(Commute.zpow_right hdσ k).eq, mul_inv_cancel_right]
  have hCnorm : C ≤ Subgroup.normalizer (Subgroup.zpowers σ : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; rw [hkey c hc x hx]; exact hx
    · intro hx
      have h := hkey c⁻¹ (C.inv_mem hc) _ hx
      have e1 : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rw [e1] at h
      rw [h]; exact hx
  have htNσ : e 4 ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set G) := by
    have hconjσ : e 4 * σ * (e 4)⁻¹ = σ⁻¹ := by rw [hinv4]; exact htσ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ y ∈ Subgroup.zpowers σ, e 4 * y * (e 4)⁻¹ ∈ Subgroup.zpowers σ := by
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← conj_zpow, hconjσ, inv_zpow]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers σ) k)
    constructor
    · exact key x
    · intro hx
      have h := key _ hx
      have e1 : e 4 * (e 4 * x * (e 4)⁻¹) * (e 4)⁻¹ = x := by
        rw [hinv4]
        calc e 4 * (e 4 * x * e 4) * e 4 = (e 4 * e 4) * x * (e 4 * e 4) := by group
          _ = x := by rw [ht2, one_mul, mul_one]
      rwa [e1] at h
  have hnorm_eq : Subgroup.normalizer (Subgroup.zpowers σ : Set G) = C ⊔ Subgroup.zpowers (e 4) := by
    apply le_antisymm
    · intro g hg
      have hgσ : g * σ * g⁻¹ ∈ Subgroup.zpowers σ :=
        (Subgroup.mem_normalizer_iff.mp hg σ).mp (Subgroup.mem_zpowers σ)
      rcases vc_zpow_three hσ3 hgσ with h | h | h
      · exfalso
        apply hσ1
        have e1 : g⁻¹ * (g * σ * g⁻¹) * g = σ := by group
        have e2 : g⁻¹ * (g * σ * g⁻¹) * g = 1 := by rw [h]; group
        exact e1.symm.trans e2
      · apply Subgroup.mem_sup_left
        rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.mp h
      · have hgσ' : g * σ = σ⁻¹ * g := mul_inv_eq_iff_eq_mul.mp h
        have hcC : e 4 * g ∈ C := by
          rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
          calc e 4 * g * σ = e 4 * (g * σ) := by group
            _ = e 4 * (σ⁻¹ * g) := by rw [hgσ']
            _ = (e 4 * σ⁻¹ * e 4) * (e 4 * g) := by
                rw [show (e 4 * σ⁻¹ * e 4) * (e 4 * g) = e 4 * σ⁻¹ * (e 4 * e 4) * g by group, ht2]
                group
            _ = σ * (e 4 * g) := by rw [← hσ']
        have hgeq : (e 4 * (e 4 * g) * (e 4)⁻¹) * e 4 = g := by
          calc (e 4 * (e 4 * g) * (e 4)⁻¹) * e 4 = (e 4 * e 4) * g * ((e 4)⁻¹ * e 4) := by group
            _ = g := by rw [ht2, one_mul, inv_mul_cancel, mul_one]
        have hmem := Subgroup.mul_mem (C ⊔ Subgroup.zpowers (e 4))
          (Subgroup.mem_sup_left (htC _ hcC)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers (e 4)))
        rwa [hgeq] at hmem
    · exact sup_le hCnorm (Subgroup.zpowers_le.mpr htNσ)
  have hMt : ∀ m ∈ M, e 4 * m * (e 4)⁻¹ ∈ M := fun m hm => hMchar (e 4) htN m hm
  have hzC_N : zOf e ∈ Subgroup.normalizer (C : Set G) := Subgroup.le_normalizer hzC
  obtain ⟨g₀, hg₀mem, hg₀⟩ := hconj
  have hg₀N : g₀ ∈ Subgroup.normalizer (C : Set G) := hLN hg₀mem
  have htz' : e 4 * zOf e = g₀ * e 4 * g₀⁻¹ := hg₀.symm
  have hcardeq : Nat.card ↥(M ⊓ Subgroup.centralizer ({e 4 * zOf e} : Set G)) =
      Nat.card ↥(M ⊓ Subgroup.centralizer ({e 4} : Set G)) := by
    have himg : (M ⊓ Subgroup.centralizer ({e 4} : Set G)).map (MulAut.conj g₀).toMonoidHom =
        M ⊓ Subgroup.centralizer ({e 4 * zOf e} : Set G) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨hxM, hxt⟩ := Subgroup.mem_inf.mp hx
        have hxt' : x * e 4 = e 4 * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
        refine Subgroup.mem_inf.mpr ⟨hMchar g₀ hg₀N x hxM, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        show g₀ * x * g₀⁻¹ * (e 4 * zOf e) = e 4 * zOf e * (g₀ * x * g₀⁻¹)
        rw [htz']
        calc g₀ * x * g₀⁻¹ * (g₀ * e 4 * g₀⁻¹) = g₀ * (x * e 4) * g₀⁻¹ := by group
          _ = g₀ * (e 4 * x) * g₀⁻¹ := by rw [hxt']
          _ = g₀ * e 4 * g₀⁻¹ * (g₀ * x * g₀⁻¹) := by group
      · intro hy
        obtain ⟨hyM, hyz⟩ := Subgroup.mem_inf.mp hy
        have hyz' : y * (e 4 * zOf e) = (e 4 * zOf e) * y :=
          Subgroup.mem_centralizer_singleton_iff.mp hyz
        rw [htz'] at hyz'
        refine ⟨g₀⁻¹ * y * g₀⁻¹⁻¹,
          Subgroup.mem_inf.mpr ⟨hMchar g₀⁻¹ (Subgroup.inv_mem _ hg₀N) y hyM, ?_⟩, ?_⟩
        · rw [Subgroup.mem_centralizer_singleton_iff]
          calc g₀⁻¹ * y * g₀⁻¹⁻¹ * e 4 = g₀⁻¹ * (y * (g₀ * e 4 * g₀⁻¹)) * g₀ := by group
            _ = g₀⁻¹ * ((g₀ * e 4 * g₀⁻¹) * y) * g₀ := by rw [hyz']
            _ = e 4 * (g₀⁻¹ * y * g₀⁻¹⁻¹) := by group
        · show g₀ * (g₀⁻¹ * y * g₀⁻¹⁻¹) * g₀⁻¹ = y
          group
    rw [← himg, Subgroup.card_map_of_injective (MulAut.conj g₀).injective]
  have hCzM : Nat.card ↥(M ⊓ Subgroup.centralizer ({zOf e} : Set G)) = 3 := by
    rw [hCz, hMH, Nat.card_zpowers, hord]
  obtain ⟨V, hVk, htV, hzV⟩ :=
    CFSG.GorensteinWalter.exists_kleinFour_of_commuting_involutions (e 4) (zOf e)
      ⟨ht1, by rw [pow_two]; exact ht2⟩ ⟨hz1, by rw [pow_two]; exact hz2⟩ hte htz
  haveI : IsKleinFour V := hVk
  have hVN : V ≤ Subgroup.normalizer (M : Set G) := by
    intro v hv
    have hv4 : v = 1 ∨ v = e 4 ∨ v = zOf e ∨ v = e 4 * zOf e := by
      by_cases h1 : v = 1
      · exact Or.inl h1
      by_cases h2 : v = e 4
      · exact Or.inr (Or.inl h2)
      by_cases h3 : v = zOf e
      · exact Or.inr (Or.inr (Or.inl h3))
      right; right; right
      have := IsKleinFour.eq_mul_of_ne_all (x := (⟨e 4, htV⟩ : V)) (y := (⟨zOf e, hzV⟩ : V))
        (z := (⟨v, hv⟩ : V))
        (fun h => ht1 (congrArg Subtype.val h)) (fun h => hz1 (congrArg Subtype.val h))
        (fun h => hte (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
        (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
      have h' := congrArg Subtype.val this
      simpa using h'
    rcases hv4 with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hMnormN _ htN
    · exact hMnormN _ hzC_N
    · exact mul_mem (hMnormN _ htN) (hMnormN _ hzC_N)
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (T := V) (K := M) hM_odd hVN
    htV hzV ht1 hz1 hte
  have hCV : Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G)) = 1 := by
    have hbot : M ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxM, hxV⟩ := Subgroup.mem_inf.mp hx
      have hxt : x * e 4 = e 4 * x :=
        ((Subgroup.mem_centralizer_iff.mp hxV) (e 4) htV).symm
      have hxz : x * zOf e = zOf e * x :=
        ((Subgroup.mem_centralizer_iff.mp hxV) (zOf e) hzV).symm
      have hxH : x ∈ H := by
        rw [← hCz]; exact Subgroup.mem_centralizer_singleton_iff.mpr hxz
      have hxσ : x ∈ Subgroup.zpowers σ := by
        rw [← hMH]; exact Subgroup.mem_inf.mpr ⟨hxM, hxH⟩
      have hσσ : σ⁻¹ ≠ σ := hσne_inv
      have hσ_ne : σ ≠ σ⁻¹ := fun h => hσne_inv h.symm
      rcases vc_zpow_three hσ3 hxσ with h | h | h
      · rw [Subgroup.mem_bot]; exact h
      · exfalso
        rw [h] at hxt
        have h1 : e 4 * σ * e 4 = σ := by
          calc e 4 * σ * e 4 = σ * e 4 * e 4 := by rw [← hxt]
            _ = σ := by rw [mul_assoc, ht2, mul_one]
        exact hσ_ne (htσ.symm.trans h1).symm
      · exfalso
        rw [h] at hxt
        have h1 : e 4 * σ⁻¹ * e 4 = σ⁻¹ := by
          calc e 4 * σ⁻¹ * e 4 = σ⁻¹ * e 4 * e 4 := by rw [← hxt]
            _ = σ⁻¹ := by rw [mul_assoc, ht2, mul_one]
        exact hσne_inv ((hσ'.trans h1).symm)
    rw [hbot, Subgroup.card_bot]
  have hBWeq : Nat.card M = Nat.card ↥(M ⊓ Subgroup.centralizer ({e 4} : Set G)) * 3 *
      Nat.card ↥(M ⊓ Subgroup.centralizer ({e 4 * zOf e} : Set G)) := by
    have h := hBW
    rw [hCV, hCzM, one_pow, mul_one] at h
    exact h
  have hdvd9 : ∀ x : G, orderOf x = 2 → Nat.card ↥(M ⊓ Subgroup.centralizer ({x} : Set G)) ∣ 9 := by
    intro x hx2
    obtain ⟨g, hg⟩ := isConj_iff.mp (hOC x hx2)
    have hgz : g * zOf e = x * g := mul_inv_eq_iff_eq_mul.mp hg
    have hgx : g⁻¹ * x * g = zOf e := by rw [← hg]; group
    have hfinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
    have hSle : (M ⊓ Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyM, hyx⟩ := Subgroup.mem_inf.mp hy
      have hyx' : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hyx
      rw [← hCz, Subgroup.mem_centralizer_singleton_iff]
      show g⁻¹ * y * g⁻¹⁻¹ * zOf e = zOf e * (g⁻¹ * y * g⁻¹⁻¹)
      calc g⁻¹ * y * g⁻¹⁻¹ * zOf e = g⁻¹ * y * (g * zOf e) := by group
        _ = g⁻¹ * y * (x * g) := by rw [hgz]
        _ = g⁻¹ * (y * x) * g := by group
        _ = g⁻¹ * (x * y) * g := by rw [hyx']
        _ = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
        _ = zOf e * (g⁻¹ * y * g⁻¹⁻¹) := by rw [hgx]; group
    have hSodd : Odd (Nat.card ↥((M ⊓ Subgroup.centralizer ({x} : Set G)).map
        (MulAut.conj g⁻¹).toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective hfinj]
      exact Odd.of_dvd_nat hM_odd (Subgroup.card_dvd_of_le inf_le_left)
    have h9 := hodd _ hSle hSodd
    rw [Subgroup.card_map_of_injective hfinj] at h9
    exact h9
  have ha9 : Nat.card ↥(M ⊓ Subgroup.centralizer ({e 4} : Set G)) ∣ 9 :=
    hdvd9 (e 4) (orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1)
  have hzt2 : (e 4 * zOf e) * (e 4 * zOf e) = 1 := by
    calc (e 4 * zOf e) * (e 4 * zOf e) = e 4 * (zOf e * e 4) * zOf e := by group
      _ = e 4 * (e 4 * zOf e) * zOf e := by rw [← htz]
      _ = (e 4 * e 4) * (zOf e * zOf e) := by group
      _ = 1 := by rw [ht2, hz2, mul_one]
  have hztne : e 4 * zOf e ≠ 1 := fun h => hte (by
    have h1 : e 4 = (zOf e)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1, inv_eq_of_mul_eq_one_right hz2])
  have hb9 : Nat.card ↥(M ⊓ Subgroup.centralizer ({e 4 * zOf e} : Set G)) ∣ 9 :=
    hdvd9 _ (orderOf_eq_prime (by rw [pow_two]; exact hzt2) hztne)
  set a := Nat.card ↥(M ⊓ Subgroup.centralizer ({e 4} : Set G)) with ha
  have hcardeq' : Nat.card M = 3 * a ^ 2 := by
    rw [hBWeq, hcardeq]; ring
  have hcard_cases : a = 1 ∨ a = 3 ∨ a = 9 := by
    have hmem : a ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨ha9, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at hmem
    simpa using hmem
  have hM3 : IsPGroup 3 M := by
    apply IsPGroup.of_card_dvd_pow (n := 5)
    rw [hcardeq']
    have h1 : a ^ 2 ∣ 9 ^ 2 := pow_dvd_pow_of_dvd ha9 2
    have h2 := mul_dvd_mul_left 3 h1
    norm_num at h2
    exact h2
  have hcardP : Nat.card (P : Subgroup ↥C) = 8 := by
    rw [hPeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0C).toEquiv, hQ0card]
  have hsyl : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ C → Nat.card R ≤ 8 := by
    intro R hR hRC
    have hR' : IsPGroup 2 (R.subgroupOf C) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hR'
    have hSP : Nat.card (S : Subgroup ↥C) = Nat.card (P : Subgroup ↥C) :=
      (Sylow.card_eq_multiplicity S).trans (Sylow.card_eq_multiplicity P).symm
    calc Nat.card R = Nat.card (R.subgroupOf C) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv).symm
      _ ≤ Nat.card (S : Subgroup ↥C) := Subgroup.card_le_of_le hS
      _ = Nat.card (P : Subgroup ↥C) := hSP
      _ = 8 := hcardP
  refine ⟨M, ⟨⟨hMC, hLC, fun c hc n hn => hMnormC c hc n hn, hM_odd, hM_inf_L, hM_union⟩,
    hM3, hMH, hMt, hnorm_eq, hcard_cases, hcardeq, hcardeq', hsyl⟩⟩


theorem leafVertexCores
    [G23Leaf LeafSylow2Cent]
    : LeafVertexCores := by
  intro G _ _ T H H₁ H₂ M e h hF hO
  have hone : G23One H H₁ H₂ := h.ctx.one
  have hlets : HLetters H H₁ H₂ e := h.lets
  obtain ⟨w, hwI, hw1, huniq⟩ := G23One.exists_unique_inf hone
  have hw2 : w * w = 1 := by rw [← pow_two]; exact G23One.sq_inf hone hwI
  have hzI : zOf e ∈ H₁ ⊓ H₂ := vc_zOf_mem_inf hlets
  have hzw : zOf e = w := by
    have hzne : zOf e ≠ 1 := by
      intro h1
      have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
      have hc : IsConj (zOf e) w := hO w hwo
      rw [h1] at hc
      exact hw1 (isConj_one_right.mp hc)
    rcases huniq (zOf e) hzI with h1 | h1
    · exact absurd h1 hzne
    · exact h1
  have hz2 : zOf e * zOf e = 1 := by rw [hzw]; exact hw2
  have hz1 : zOf e ≠ 1 := by rw [hzw]; exact hw1
  have hzL2 : zOf e ∈ H₂ := (Subgroup.mem_inf.mp hzI).2
  have hzL1 : zOf e ∈ H₁ := (Subgroup.mem_inf.mp hzI).1
  have hCz : Subgroup.centralizer ({zOf e} : Set G) = H := by
    apply le_antisymm
    · intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      rw [hone.eq_centralizer, Subgroup.mem_centralizer_iff]
      intro y hy
      rcases huniq y hy with rfl | rfl
      · simp
      · rw [hzw] at hc; exact hc.symm
    · intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact G23One.mul_comm_of_mem_inf hone hc hzI
  obtain ⟨eL2⟩ := hone.iso_two
  obtain ⟨eL1⟩ := hone.iso_one
  have hcardH : 24 < Nat.card H := by rw [hF.card_H]; norm_num
  have r0 : e 0 * e 0 * e 0 = 1 := by
    have := h.lets.rels [(0, true), (0, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have r2 : e 2 * e 2 * e 2 = 1 := by
    have := h.lets.rels [(2, true), (2, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have r11 : e 4 * e 4 = 1 := by
    have := h.lets.rels [(4, true), (4, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have r12 : e 4 * e 0 * e 4 * e 0 = 1 := by
    have := h.lets.rels [(4, true), (0, true), (4, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have r14 : e 4 * e 2 * e 4 * e 2 = 1 := by
    have := h.lets.rels [(4, true), (2, true), (4, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have ht : e 4 ∈ H := by
    rw [← hlets.gen]; exact Subgroup.subset_closure ⟨4, rfl⟩
  have ht2 : e 4 * e 4 = 1 := r11
  have ht1 : e 4 ≠ 1 := by
    intro h1
    obtain ⟨g, -, hg⟩ := hF.conj_t₂
    rw [h1, mul_one, mul_inv_cancel, one_mul] at hg
    exact hz1 hg.symm
  have hte : e 4 ≠ zOf e := by
    intro h1
    obtain ⟨g, -, hg⟩ := hF.conj_t₂
    rw [h1, hz2] at hg
    apply hz1
    have e1 : g⁻¹ * (g * zOf e * g⁻¹) * g = zOf e := by group
    have e2 : g⁻¹ * (g * zOf e * g⁻¹) * g = 1 := by rw [hg]; group
    exact e1.symm.trans e2
  have hσ1 : e 0 ≠ 1 := vc_ne_one hF.cent₁ hcardH (vc_card_L eL2)
  have hσ3 : e 0 ^ 3 = 1 := by rw [pow_three']; exact r0
  have htσ0 : e 4 * e 0 * e 4 = (e 0)⁻¹ := eq_inv_of_mul_eq_one_left r12
  obtain ⟨M₁, hM₁⟩ := vc_vertexCore (L := H₂) (e := e) (σ := e 0) eL2 hzL2 hz1 hz2 hCz hσ3 hσ1
    hF.cent₁ hF.disj₁ ht ht2 ht1 hte htσ0 hF.conj_t₂
    (fun S hS hodd => (hF.odd_sub S hS hodd).1) (fun x hx => hO x hx)
  have hσ1' : e 2 ≠ 1 := vc_ne_one hF.cent₂ hcardH (vc_card_L eL1)
  have hσ3' : e 2 ^ 3 = 1 := by rw [pow_three']; exact r2
  have htσ2 : e 4 * e 2 * e 4 = (e 2)⁻¹ := eq_inv_of_mul_eq_one_left r14
  obtain ⟨M₂, hM₂⟩ := vc_vertexCore (L := H₁) (e := e) (σ := e 2) eL1 hzL1 hz1 hz2 hCz hσ3' hσ1'
    hF.cent₂ hF.disj₂ ht ht2 ht1 hte htσ2 hF.conj_t₁
    (fun S hS hodd => (hF.odd_sub S hS hodd).1) (fun x hx => hO x hx)
  exact ⟨M₁, M₂, hM₁, hM₂⟩

end CFSG.GH74.QTGen4.Recog.G23.P7

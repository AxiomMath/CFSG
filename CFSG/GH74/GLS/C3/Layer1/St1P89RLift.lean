module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.GH74.GLS.C3.Layer1.Back93

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.ComponentClassification CFSG.GH74.GLS.C3.Layer1
open scoped Pointwise

section Lift

variable {G : Type} [Group G] [Finite G]

private theorem factorization_two_mul_odd' {a b : ℕ} (ha : a ≠ 0) (hb : Odd b) :
    (a * b).factorization 2 = a.factorization 2 := by
  have hb0 : b ≠ 0 := hb.pos.ne'
  have hb2 : b.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hb)
  rw [Nat.factorization_mul ha hb0, Finsupp.add_apply, hb2, add_zero]


omit [Finite G] in
private theorem mem_zpowers_of_sq' {a g : G} (ha : a ^ 2 = 1) (hg : g ∈ zpowers a) : g = 1 ∨ g = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    show a ^ (2 * m) = 1
    rw [zpow_mul, zpow_two, ← pow_two, ha, one_zpow]
  · right
    show a ^ (2 * m + 1) = a
    rw [zpow_add, zpow_mul, zpow_two, ← pow_two, ha, one_zpow, one_mul, zpow_one]

theorem exists_normalizer_lift {K : Subgroup G} {f : G} {V : Subgroup G} (hVK : V ≤ K)
    (hV2 : IsPGroup 2 ↥V) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hfV : ∀ v ∈ V, f * v = v * f) {n₀ : G} (hn₀ : n₀ ∈ K) (hfn : f * n₀ = n₀ * f)
    (hact : ∀ v ∈ V, ∃ v' ∈ V, n₀ * v * n₀⁻¹ * v'⁻¹ ∈ pPrimeCoreOf 2 K) :
    ∃ n ∈ K, f * n = n * f ∧ ∀ v ∈ V, ∃ v' ∈ V, n * v * n⁻¹ = v' ∧
      n₀ * v * n₀⁻¹ * v'⁻¹ ∈ pPrimeCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := pPrimeCoreOf 2 K with hO
  have hOK : O ≤ K := TwoThin.pPrimeCoreOf_le K
  have hOn : ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho =>
    TwoThin.pPrimeCoreOf_normalized K hk ho
  have hOodd : Odd (Nat.card ↥O) := TwoThin.card_pPrimeCoreOf_odd K
  set O' : Subgroup G := O ⊓ centralizer ({f} : Set G) with hO'
  have hO'f : ∀ o ∈ O', Commute f o := fun o ho =>
    (mem_centralizer_singleton_iff.1 ho.2).symm
  have hfV' : ∀ v ∈ V, Commute f v := hfV
  have hfn' : Commute f n₀ := hfn
  have hconj : ∀ v ∈ V, ∀ o ∈ O', v * o * v⁻¹ ∈ O' := by
    intro v hv o ho
    refine ⟨hOn v (hVK hv) o ho.1, mem_centralizer_singleton_iff.2 ?_⟩
    exact (((hfV' v hv).mul_right (hO'f o ho)).mul_right (hfV' v hv).inv_right).eq.symm
  have hVn : V ≤ normalizer (O' : Set G) := by
    intro v hv
    refine mem_normalizer_iff.2 fun h => ⟨fun hh => hconj v hv h hh, fun hh => ?_⟩
    have := hconj v⁻¹ (V.inv_mem hv) _ hh
    rwa [show v⁻¹ * (v * h * v⁻¹) * v⁻¹⁻¹ = h by group] at this
  set H : Subgroup G := O' ⊔ V with hH
  have hHprod : ((H : Subgroup G) : Set G) = (O' : Set G) * (V : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left O' V hVn
  have hmemH : ∀ h ∈ H, ∃ o ∈ O', ∃ v ∈ V, h = o * v := by
    intro h hh
    have : h ∈ (O' : Set G) * (V : Set G) := by rw [← hHprod]; exact hh
    obtain ⟨o, ho, v, hv, rfl⟩ := this
    exact ⟨o, ho, v, hv, rfl⟩
  have hHK : H ≤ K ⊓ centralizer ({f} : Set G) := by
    refine sup_le (fun o ho => ⟨hOK ho.1, ho.2⟩) (fun v hv => ⟨hVK hv, mem_centralizer_singleton_iff.2 ?_⟩)
    exact (hfV v hv).symm
  have hO'odd : Odd (Nat.card ↥O') :=
    Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le (inf_le_left : O' ≤ O))
  obtain ⟨m, hm⟩ := hV2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥O') (Nat.card ↥V) := by
    rw [hm]
    exact (Nat.coprime_two_left.2 hO'odd).symm.pow_right m
  have hcard_le : Nat.card ↥H ≤ Nat.card ↥O' * Nat.card ↥V := by
    let φ : ↥O' × ↥V → ↥H := fun p =>
      ⟨p.1 * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
    have hsurj : Function.Surjective φ := by
      rintro ⟨h, hh⟩
      obtain ⟨o, ho, v, hv, rfl⟩ := hmemH h hh
      exact ⟨(⟨o, ho⟩, ⟨v, hv⟩), rfl⟩
    have := Nat.card_le_card_of_surjective φ hsurj
    rwa [Nat.card_prod] at this
  have hcard_ge : Nat.card ↥O' * Nat.card ↥V ≤ Nat.card ↥H := by
    have hd1 : Nat.card ↥O' ∣ Nat.card ↥H := Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card ↥V ∣ Nat.card ↥H := Subgroup.card_dvd_of_le le_sup_right
    exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd hd1 hd2)
  have hcardH : Nat.card ↥H = Nat.card ↥O' * Nat.card ↥V := le_antisymm hcard_le hcard_ge
  have hSyl : IsSylowOf 2 V H := by
    refine isSylowOf_of_card le_sup_right ?_
    rw [hcardH, mul_comm, hm, factorization_two_mul_odd' (by positivity) hO'odd,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hV'le : V.map (MulAut.conj n₀).toMonoidHom ≤ H := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨v', hv', hOo⟩ := hact v hv
    have ho' : n₀ * v * n₀⁻¹ * v'⁻¹ ∈ O' := by
      refine ⟨hOo, mem_centralizer_singleton_iff.2 ?_⟩
      exact ((((hfn'.mul_right (hfV' v hv)).mul_right hfn'.inv_right).mul_right
        (hfV' v' hv').inv_right).eq).symm
    have e : (MulAut.conj n₀).toMonoidHom v = (n₀ * v * n₀⁻¹ * v'⁻¹) * v' := by
      simp [MulAut.conj_apply]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho') (Subgroup.mem_sup_right hv')
  obtain ⟨k, hkH, hk⟩ := FooteLit.exists_conj_le_of_isSylowOf hSyl hV'le (hV2.map _)
  obtain ⟨o₁, ho₁, v₁, hv₁, hkinv⟩ := hmemH k⁻¹ (H.inv_mem hkH)
  have hkK : k ∈ K := (hHK hkH).1
  have hkf : Commute f k := (mem_centralizer_singleton_iff.1 (hHK hkH).2).symm
  refine ⟨k⁻¹ * n₀, K.mul_mem (K.inv_mem hkK) hn₀, (hkf.inv_right.mul_right hfn').eq, ?_⟩
  intro v hv
  have hvmem : k⁻¹ * (n₀ * v * n₀⁻¹) * k ∈ V := by
    apply hk
    exact ⟨v, hv, by simp [MulAut.conj_apply]⟩
  refine ⟨k⁻¹ * (n₀ * v * n₀⁻¹) * k, hvmem, by group, ?_⟩
  obtain ⟨v₂, hv₂, hOo₂⟩ := hact v hv
  have hv12 : v₁ * v₂ = v₂ * v₁ := hVc v₁ hv₁ v₂ hv₂
  have hc : v₂ * v₁⁻¹ = v₁⁻¹ * v₂ := by
    have : Commute v₂ v₁ := hv12.symm
    exact this.inv_right.eq
  set w : G := n₀ * v * n₀⁻¹ with hw
  have ho₂ : w * v₂⁻¹ ∈ O := hOo₂
  have ho₁O : o₁ ∈ O := ho₁.1
  have ho₃ : (k⁻¹ * w * k) * v₂⁻¹ ∈ O := by
    have e : (k⁻¹ * w * k) * v₂⁻¹ =
        o₁ * (v₁ * (w * v₂⁻¹) * v₁⁻¹) * (v₂ * o₁⁻¹ * v₂⁻¹) := by
      have hk' : k = (o₁ * v₁)⁻¹ := by rw [← hkinv, inv_inv]
      rw [hk']
      calc _ = o₁ * v₁ * w * v₁⁻¹ * o₁⁻¹ * v₂⁻¹ := by group
        _ = o₁ * v₁ * (w * v₂⁻¹) * (v₂ * v₁⁻¹) * o₁⁻¹ * v₂⁻¹ := by group
        _ = o₁ * v₁ * (w * v₂⁻¹) * (v₁⁻¹ * v₂) * o₁⁻¹ * v₂⁻¹ := by rw [hc]
        _ = _ := by group
    rw [e]
    exact O.mul_mem (O.mul_mem ho₁O (hOn v₁ (hVK hv₁) _ ho₂))
      (hOn v₂ (hVK hv₂) _ (O.inv_mem ho₁O))
  have e2 : w * (k⁻¹ * w * k)⁻¹ = (w * v₂⁻¹) * ((k⁻¹ * w * k) * v₂⁻¹)⁻¹ := by group
  rw [e2]
  exact O.mul_mem ho₂ (O.inv_mem ho₃)


theorem exists_normalizer_lift_klein {K : Subgroup G} {f z s z' s' n₀ : G} (hzK : z ∈ K)
    (hsK : s ∈ K) (hz2 : z ^ 2 = 1) (hs2 : s ^ 2 = 1) (hzs : z * s = s * z)
    (hz'V : z' ∈ zpowers z ⊔ zpowers s) (hs'V : s' ∈ zpowers z ⊔ zpowers s)
    (hfz : f * z = z * f) (hfs : f * s = s * f) (hn₀ : n₀ ∈ K) (hfn : f * n₀ = n₀ * f)
    (h1 : n₀ * z * n₀⁻¹ * z'⁻¹ ∈ pPrimeCoreOf 2 K) (h2 : n₀ * s * n₀⁻¹ * s'⁻¹ ∈ pPrimeCoreOf 2 K) :
    ∃ n ∈ K, f * n = n * f ∧ n * z * n⁻¹ = z' ∧ n * s * n⁻¹ = s' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := zpowers z ⊔ zpowers s with hV
  set O : Subgroup G := pPrimeCoreOf 2 K with hO
  have hOn : ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho =>
    TwoThin.pPrimeCoreOf_normalized K hk ho
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers s, a * b = b * a := by
    intro a ha b hb
    rcases mem_zpowers_of_sq' hz2 ha with rfl | rfl <;> rcases mem_zpowers_of_sq' hs2 hb with rfl | rfl <;>
      simp [hzs]
  have hVlist : ∀ g ∈ V, g = 1 ∨ g = z ∨ g = s ∨ g = z * s := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm hg
    rcases mem_zpowers_of_sq' hz2 ha with rfl | rfl <;> rcases mem_zpowers_of_sq' hs2 hb with rfl | rfl <;>
      simp
  have hzV : z ∈ V := Subgroup.mem_sup_left (mem_zpowers z)
  have hsV : s ∈ V := Subgroup.mem_sup_right (mem_zpowers s)
  have hVK : V ≤ K := sup_le (zpowers_le.2 hzK) (zpowers_le.2 hsK)
  have hzs' : Commute z s := hzs
  have hcz : ∀ g ∈ V, Commute z g := by
    intro g hg
    rcases hVlist g hg with hh | hh | hh | hh <;> subst g
    · exact Commute.one_right z
    · exact Commute.refl z
    · exact hzs'
    · exact (Commute.refl z).mul_right hzs'
  have hcs : ∀ g ∈ V, Commute s g := by
    intro g hg
    rcases hVlist g hg with hh | hh | hh | hh <;> subst g
    · exact Commute.one_right s
    · exact hzs'.symm
    · exact Commute.refl s
    · exact hzs'.symm.mul_right (Commute.refl s)
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    rcases hVlist a ha with hh | hh | hh | hh <;> subst a
    · simp
    · exact (hcz b hb).eq
    · exact (hcs b hb).eq
    · exact ((hcz b hb).mul_left (hcs b hb)).eq
  have hV2 : IsPGroup 2 ↥V := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨g, hg⟩ := g
    apply Subtype.ext
    show g ^ 2 ^ 1 = 1
    rw [pow_one]
    rcases hVlist g hg with hh | hh | hh | hh <;> subst g
    · simp
    · exact hz2
    · exact hs2
    · rw [hzs'.mul_pow, hz2, hs2, one_mul]
  have hfV : ∀ v ∈ V, f * v = v * f := by
    intro v hv
    have hfz' : Commute f z := hfz
    have hfs' : Commute f s := hfs
    rcases hVlist v hv with hh | hh | hh | hh <;> subst v
    · simp
    · exact hfz
    · exact hfs
    · exact (hfz'.mul_right hfs').eq
  have hmul : ∀ a a' b b' : G, a ∈ K → b ∈ K → a' ∈ K → a * a'⁻¹ ∈ O → b * b'⁻¹ ∈ O →
      a * b * (a' * b')⁻¹ ∈ O := by
    intro a a' b b' haK hbK ha'K ha hb
    have : a * b * (a' * b')⁻¹ = (a * (b * b'⁻¹) * a⁻¹) * (a * a'⁻¹) := by group
    rw [this]
    exact O.mul_mem (hOn a haK _ hb) ha
  have hact : ∀ v ∈ V, ∃ v' ∈ V, n₀ * v * n₀⁻¹ * v'⁻¹ ∈ O := by
    intro v hv
    rcases hVlist v hv with hh | hh | hh | hh <;> subst v
    · exact ⟨1, V.one_mem, by simp⟩
    · exact ⟨z', hz'V, h1⟩
    · exact ⟨s', hs'V, h2⟩
    · refine ⟨z' * s', V.mul_mem hz'V hs'V, ?_⟩
      have e : n₀ * (z * s) * n₀⁻¹ = (n₀ * z * n₀⁻¹) * (n₀ * s * n₀⁻¹) := by group
      rw [e]
      have hzK' : n₀ * z * n₀⁻¹ ∈ K := K.mul_mem (K.mul_mem hn₀ hzK) (K.inv_mem hn₀)
      have hz'K : z' ∈ K := hVK hz'V
      exact hmul _ _ _ _ hzK' (K.mul_mem (K.mul_mem hn₀ hsK) (K.inv_mem hn₀)) hz'K h1 h2
  obtain ⟨n, hnK, hfnn, hn⟩ := exists_normalizer_lift hVK hV2 hVc hfV hn₀ hfn hact
  have hVO : V ⊓ O = ⊥ := Back.Setup91.inf_pPrimeCoreOf_eq_bot K hV2
  have key : ∀ (w w' : G), w ∈ V → w' ∈ V → ∀ A : G, A * w⁻¹ ∈ O → A * w'⁻¹ ∈ O → w = w' := by
    intro w w' hw hw' A hA hA'
    have h3 : w * w'⁻¹ ∈ V ⊓ O := by
      refine ⟨V.mul_mem hw (V.inv_mem hw'), ?_⟩
      have : w * w'⁻¹ = (A * w⁻¹)⁻¹ * (A * w'⁻¹) := by group
      rw [this]
      exact O.mul_mem (O.inv_mem hA) hA'
    rw [hVO, Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.1 h3
  refine ⟨n, hnK, hfnn, ?_, ?_⟩
  · obtain ⟨vz, hvz, hnz, hOz⟩ := hn z hzV
    rw [hnz]
    exact key vz z' hvz hz'V _ hOz h1
  · obtain ⟨vs, hvs, hns, hOs⟩ := hn s hsV
    rw [hns]
    exact key vs s' hvs hs'V _ hOs h2

end Lift

end CFSG.GH74.GLS.C3.Layer1.P89

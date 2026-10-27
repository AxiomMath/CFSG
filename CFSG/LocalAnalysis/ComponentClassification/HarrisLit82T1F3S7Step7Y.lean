module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Step7

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {z : G} {L S : Subgroup G}

namespace Step6Three

variable (d : Step6Three z L S)

abbrev M : Subgroup G := centralizer {z} ⊓ centralizer {d.z₁}

abbrev OM : Subgroup G := (pPrimeCore 2 ↥d.M).map d.M.subtype

omit [Finite G] in
theorem isSolvableTwoComponentIn_map_conj {r : G}
    (hMr : d.M.map (MulAut.conj r).toMonoidHom = d.M) {J : Subgroup G}
    (hJ : IsSolvableTwoComponentIn J d.M) :
    IsSolvableTwoComponentIn (J.map (MulAut.conj r).toMonoidHom) d.M := by
  have h1 := isSolvableTwoComponentIn_map_mulEquiv (MulAut.conj r) hJ
  rwa [hMr] at h1

omit [Finite G] in
theorem map_conj_b (hc : z * d.z₁ = d.z₁ * z) :
    d.M.map (MulAut.conj d.b).toMonoidHom = d.M ∧
      d.J₁.map (MulAut.conj d.b).toMonoidHom = d.J₃ ∧
      d.J₂.map (MulAut.conj d.b).toMonoidHom = d.J₂ ∧
      d.J₃.map (MulAut.conj d.b).toMonoidHom = d.J₁ := by
  have hMb : d.M.map (MulAut.conj d.b).toMonoidHom = d.M := by
    change (centralizer ({z} : Set G) ⊓ centralizer {d.z₁}).map (MulAut.conj d.b).toMonoidHom =
      centralizer {z} ⊓ centralizer {d.z₁}
    rw [Subgroup.map_inf _ _ _ (MulAut.conj d.b).injective, map_centralizer_singleton_mulEquiv,
      map_centralizer_singleton_mulEquiv, MulAut.conj_apply, MulAut.conj_apply, d.hbz, d.hbz₁,
      inf_comm (centralizer {z * d.z₁}) (centralizer {d.z₁}), hc, T23.centralizer_inf_mul,
      inf_comm (centralizer {d.z₁}) (centralizer {z})]
  have hz₁z₁ : d.z₁ * d.z₁ = 1 := by rw [← sq, ← d.hz₁, pow_orderOf_eq_one]
  have hbzz₁ : d.b * (z * d.z₁) * d.b⁻¹ = z := by
    calc d.b * (z * d.z₁) * d.b⁻¹ = (d.b * z * d.b⁻¹) * (d.b * d.z₁ * d.b⁻¹) := by group
      _ = z := by rw [d.hbz, d.hbz₁, mul_assoc, hz₁z₁, mul_one]
  exact ⟨hMb, d.uniq₃ _ (d.isSolvableTwoComponentIn_map_conj hMb d.hJ₁) ⟨z, d.hzJ₁, d.hbz⟩,
    d.uniq₂ _ (d.isSolvableTwoComponentIn_map_conj hMb d.hJ₂) ⟨d.z₁, d.hz₁J₂, d.hbz₁⟩,
    d.uniq₁ _ (d.isSolvableTwoComponentIn_map_conj hMb d.hJ₃) ⟨z * d.z₁, d.hzz₁J₃, hbzz₁⟩⟩

@[expose] def Y : Subgroup G where
  carrier := {r | r ∈ d.M ∧ ∀ j : G, (j ∈ d.J₁ ∨ j ∈ d.J₂ ∨ j ∈ d.J₃) →
    r * j * r⁻¹ * j⁻¹ ∈ d.OM}
  mul_mem' {a c} ha hc := by
    refine ⟨mul_mem ha.1 hc.1, fun j hj => ?_⟩
    have h1 := ha.2 j hj
    have h2 := conj_mem_pPrimeCore_map ha.1 (hc.2 j hj)
    have h3 : a * c * j * (a * c)⁻¹ * j⁻¹ =
        a * (c * j * c⁻¹ * j⁻¹) * a⁻¹ * (a * j * a⁻¹ * j⁻¹) := by group
    rw [h3]
    exact mul_mem h2 h1
  one_mem' := ⟨one_mem _, fun j _ => by simp⟩
  inv_mem' {a} ha := by
    refine ⟨inv_mem ha.1, fun j hj => ?_⟩
    have h1 := conj_mem_pPrimeCore_map (inv_mem ha.1) (inv_mem (ha.2 j hj))
    have h3 : a⁻¹ * j * a⁻¹⁻¹ * j⁻¹ = a⁻¹ * (a * j * a⁻¹ * j⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [h3]
    exact h1

omit [Finite G] in
theorem mem_Y {r : G} : r ∈ d.Y ↔ r ∈ d.M ∧ ∀ j : G, (j ∈ d.J₁ ∨ j ∈ d.J₂ ∨ j ∈ d.J₃) →
    r * j * r⁻¹ * j⁻¹ ∈ d.OM :=
  Iff.rfl

theorem conj_b_mem_Y (hc : z * d.z₁ = d.z₁ * z) {r : G} (hr : r ∈ d.Y) :
    d.b * r * d.b⁻¹ ∈ d.Y := by
  obtain ⟨hMb, h₁, h₂, h₃⟩ := d.map_conj_b hc
  obtain ⟨hrM, hrJ⟩ := (d.mem_Y).mp hr
  refine (d.mem_Y).mpr ⟨?_, fun j hj => ?_⟩
  · rw [← hMb]
    exact ⟨r, hrM, rfl⟩
  · have hback : ∀ {J J' : Subgroup G}, J'.map (MulAut.conj d.b).toMonoidHom = J → j ∈ J →
        d.b⁻¹ * j * d.b ∈ J' := by
      intro J J' hJJ hjJ
      rw [← hJJ] at hjJ
      obtain ⟨j', hj', rfl⟩ := hjJ
      have h1 : d.b⁻¹ * ((MulAut.conj d.b).toMonoidHom j') * d.b = j' := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [h1]
      exact hj'
    have hj' : d.b⁻¹ * j * d.b ∈ d.J₁ ∨ d.b⁻¹ * j * d.b ∈ d.J₂ ∨ d.b⁻¹ * j * d.b ∈ d.J₃ := by
      rcases hj with hj | hj | hj
      · exact .inr (.inr (hback h₃ hj))
      · exact .inr (.inl (hback h₂ hj))
      · exact .inl (hback h₁ hj)
    have h2 := conj_mem_pPrimeCore_map_of_map_eq hMb (hrJ _ hj')
    rw [show d.b * (r * (d.b⁻¹ * j * d.b) * r⁻¹ * (d.b⁻¹ * j * d.b)⁻¹) * d.b⁻¹ =
      d.b * r * d.b⁻¹ * j * (d.b * r * d.b⁻¹)⁻¹ * j⁻¹ by group] at h2
    exact h2

theorem inf_Q_le_Y (hI : S7Inputs) (h : S7Config G z L)
    (hS : IsSylowOf 2 S (centralizer {z})) :
    S ⊓ (centralizer {z} ⊓ coreActionKernel L) ≤ d.Y := by
  intro s hs
  obtain ⟨hsS, hsQ⟩ := mem_inf.mp hs
  obtain ⟨hsz, hsK⟩ := mem_inf.mp hsQ
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  have hON : ∀ x ∈ centralizer ({z} : Set G), ∀ o ∈ (pPrimeCore 2 ↥L).map L.subtype,
      x * o * x⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := fun x hx o ho =>
    (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L
      (pPrimeCore 2 ↥L) (hHN hx)) o).mp ho
  have hsz₁ : s * d.z₁ = d.z₁ * s :=
    commute_of_mem_coreActionKernel hS.isPGroup hsS hsK d.hz₁S d.hz₁L
  have hsM : s ∈ d.M := mem_inf.mpr ⟨hsz, mem_centralizer_singleton_iff.mpr hsz₁⟩
  have hcomm : ∀ l ∈ L, l ∈ d.M → s * l * s⁻¹ * l⁻¹ ∈ d.OM := by
    intro l hlL hlM
    have h1 : l⁻¹ * s * l * s⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := by
      have h2 := (mem_coreActionKernel.mp (inv_mem hsK)).2 l hlL
      rwa [inv_inv] at h2
    have h2 : s * l * s⁻¹ * l⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := by
      have h3 := hON l (h.hL.1 hlL) _ h1
      rwa [show l * (l⁻¹ * s * l * s⁻¹) * l⁻¹ = s * l * s⁻¹ * l⁻¹ by group] at h3
    have hM : s * l * s⁻¹ * l⁻¹ ∈ d.M :=
      mul_mem (mul_mem (mul_mem hsM hlM) (inv_mem hsM)) (inv_mem hlM)
    exact ⟨⟨_, hM⟩, mem_pPrimeCore_of_normal (fun m hm o ho => hON m (mem_inf.mp hm).1 o ho)
      (odd_card_pPrimeCore_map L) hM h2, rfl⟩
  refine (d.mem_Y).mpr ⟨hsM, fun j hj => ?_⟩
  have hjLO : j ∈ L ⊔ d.OM := by
    rcases hj with hj | hj | hj
    exacts [d.hJ₁L hj, d.hJ₂L hj, d.hJ₃L hj]
  have hjM : j ∈ d.M := by
    rcases hj with hj | hj | hj
    exacts [d.hJ₁.1 hj, d.hJ₂.1 hj, d.hJ₃.1 hj]
  have hOMN : d.OM ≤ normalizer (L : Set G) := (map_subtype_le _).trans (inf_le_left.trans hHN)
  have hjs : j ∈ ((L ⊔ d.OM : Subgroup G) : Set G) := hjLO
  rw [coe_mul_of_right_le_normalizer_left L d.OM hOMN] at hjs
  obtain ⟨l, hl, o, ho, rfl⟩ := hjs
  have hoM : o ∈ d.M := map_subtype_le _ ho
  have hlM : l ∈ d.M := by
    have h1 := mul_mem hjM (inv_mem hoM)
    rwa [mul_inv_cancel_right] at h1
  have h1 := hcomm l hl hlM
  have h2 : s * o * s⁻¹ * o⁻¹ ∈ d.OM := mul_mem (conj_mem_pPrimeCore_map hsM ho) (inv_mem ho)
  have h3 : l * (s * o * s⁻¹ * o⁻¹) * l⁻¹ ∈ d.OM := conj_mem_pPrimeCore_map hlM h2
  have h4 : s * (l * o) * s⁻¹ * (l * o)⁻¹ =
      (s * l * s⁻¹ * l⁻¹) * (l * (s * o * s⁻¹ * o⁻¹) * l⁻¹) := by group
  show s * (l * o) * s⁻¹ * (l * o)⁻¹ ∈ d.OM
  rw [h4]
  exact mul_mem h1 h3

theorem mem_Q_of_mem_Y (hI : S7Inputs) (h : S7Config G z L) {r : G} (hr : r ∈ d.Y) :
    r ∈ coreActionKernel L ∨ r * d.z₁⁻¹ ∈ coreActionKernel L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hrM, hrJ⟩ := (d.mem_Y).mp hr
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  have hrN : r ∈ normalizer (L : Set G) := hHN (mem_inf.mp hrM).1
  have hz₁' : orderOf (⟨d.z₁, d.hz₁L⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact d.hz₁
  have hz₁sq : (⟨d.z₁, d.hz₁L⟩ : ↥L) * ⟨d.z₁, d.hz₁L⟩ = 1 := by
    rw [← sq, ← hz₁', pow_orderOf_eq_one]
  set t : Bar L := QuotientGroup.mk ⟨d.z₁, d.hz₁L⟩ with ht
  have ht2 : orderOf t = 2 := orderOf_mk_eq_two (odd_card_pPrimeCore_two ↥L) hz₁'
  obtain ⟨hO1, hU2⟩ :=
    harris82Lemma411U2Three_holds (Bar L) 3 1 Nat.prime_three (by norm_num) h.hcov t ht2 d.hz₁Z
  have hCt : (centralizer ({⟨d.z₁, d.hz₁L⟩} : Set ↥L)).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) =
      centralizer {t} := map_centralizer_eq (odd_card_pPrimeCore_two ↥L) hz₁sq
  have hOML : ∀ {c : G} (hc : c ∈ d.OM) (hcL : c ∈ L), (⟨c, hcL⟩ : ↥L) ∈ pPrimeCore 2 ↥L := by
    intro c hc hcL
    set N : Subgroup (Bar L) :=
      ((d.OM ⊓ L).subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) with hN
    have hNC : N ≤ centralizer {t} := by
      rintro _ ⟨⟨o, hoL⟩, ho, rfl⟩
      rw [← hCt]
      refine ⟨⟨o, hoL⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hoM : o ∈ d.M := map_subtype_le _ (mem_inf.mp ho).1
      exact mem_centralizer_singleton_iff.mp (mem_inf.mp hoM).2
    have hnorm : ∀ m ∈ centralizer {t}, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
      intro m hm n hn
      rw [← hCt] at hm
      obtain ⟨y, hy, rfl⟩ := hm
      obtain ⟨⟨o, hoL⟩, ho, rfl⟩ := hn
      have hyM : (y : G) ∈ d.M := mem_inf.mpr ⟨h.hL.1 y.2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
      have ho' := mem_inf.mp ho
      refine ⟨y * ⟨o, hoL⟩ * y⁻¹, mem_inf.mpr ⟨conj_mem_pPrimeCore_map hyM ho'.1,
        mul_mem (mul_mem y.2 hoL) (inv_mem y.2)⟩, ?_⟩
      simp only [map_mul, map_inv]
    have hNodd : Odd (Nat.card N) := by
      have h1 : Nat.card N ∣ Nat.card ↥((d.OM ⊓ L).subgroupOf L) := Subgroup.card_map_dvd _ _
      have h2 : Nat.card ↥((d.OM ⊓ L).subgroupOf L) ∣ Nat.card ↥d.OM := by
        rw [← Subgroup.card_map_of_injective L.subtype_injective, subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)
      exact (odd_card_pPrimeCore_map d.M).of_dvd_nat (h1.trans h2)
    have hcN : (QuotientGroup.mk ⟨c, hcL⟩ : Bar L) ∈ N := ⟨⟨c, hcL⟩, mem_inf.mpr ⟨hc, hcL⟩, rfl⟩
    have h1 := mem_pPrimeCore_of_normal hnorm hNodd (hNC hcN) hcN
    rw [hO1, mem_bot] at h1
    have h2 : (QuotientGroup.mk ⟨c, hcL⟩ : Bar L) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hfix : ∀ J : Subgroup (Bar L), IsSolvableTwoComponentIn J (centralizer {t}) →
      ∀ j ∈ J, barAction L ⟨r, hrN⟩ j = j := by
    intro J hJ j hj
    obtain ⟨⟨j₀, hj₀L⟩, hj₀, rfl⟩ := d.hcover J hJ j hj
    have hc := hrJ j₀ hj₀
    have hrj : r * j₀ * r⁻¹ ∈ L := (mem_normalizer_iff.mp hrN j₀).mp hj₀L
    have hcL : r * j₀ * r⁻¹ * j₀⁻¹ ∈ L := mul_mem hrj (inv_mem hj₀L)
    have hcO := hOML hc hcL
    rw [barAction_mk, QuotientGroup.eq]
    have h1 : (normalizerConj L ⟨r, hrN⟩ ⟨j₀, hj₀L⟩)⁻¹ * ⟨j₀, hj₀L⟩ =
        (⟨j₀, hj₀L⟩ : ↥L)⁻¹ * (⟨_, hcL⟩ : ↥L)⁻¹ * ((⟨j₀, hj₀L⟩ : ↥L)⁻¹)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply, inv_inv]
      group
    rw [h1]
    exact (inferInstance : (pPrimeCore 2 ↥L).Normal).conj_mem _ (inv_mem hcO) _
  rcases hU2 (barAction L ⟨r, hrN⟩) hfix with hα | hα
  · exact .inl ((mem_ker_barAction L ⟨r, hrN⟩).mp (MonoidHom.mem_ker.mpr hα))
  · right
    have hz₁N : d.z₁ ∈ normalizer (L : Set G) := le_normalizer d.hz₁L
    have h1 : barAction L ⟨d.z₁, hz₁N⟩ = MulAut.conj t :=
      barAction_of_mem L ⟨d.z₁, d.hz₁L⟩ hz₁N
    have h2 : barAction L ⟨r * d.z₁⁻¹, mul_mem hrN (inv_mem hz₁N)⟩ = 1 := by
      have h3 : (⟨r * d.z₁⁻¹, mul_mem hrN (inv_mem hz₁N)⟩ : ↥(normalizer (L : Set G))) =
          ⟨r, hrN⟩ * (⟨d.z₁, hz₁N⟩)⁻¹ := rfl
      rw [h3, map_mul, map_inv, hα, h1]
      exact mul_inv_cancel _
    exact (mem_ker_barAction L _).mp (MonoidHom.mem_ker.mpr h2)

end Step6Three

end CFSG.ComponentClassification.HarrisLit.T1

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Cen
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Order13

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup

section Gen

variable {G : Type} [Group G]

theorem sq_eq_one_of_orderOf_two {g : G} (h : orderOf g = 2) : g * g = 1 := by
  rw [← pow_two, ← h]
  exact pow_orderOf_eq_one g

theorem centralizer_eq_of_generate {S T : Set G} (h1 : ∀ s ∈ S, s ∈ closure T)
    (h2 : ∀ t ∈ T, t ∈ closure S) : centralizer S = centralizer T := by
  apply centralizer_eq_of_closure_eq
  exact le_antisymm ((closure_le _).2 h1) ((closure_le _).2 h2)

theorem centralizer_pair_part {z w l : G} (hw : w = l ∨ w = z * l) :
    centralizer ({z, w} : Set G) = centralizer ({z, l} : Set G) := by
  apply centralizer_eq_of_generate
  · intro s hs
    rcases hs with hs | hs
    · rw [hs]; exact subset_closure (by simp)
    · rw [Set.mem_singleton_iff.1 hs]
      rcases hw with hw | hw
      · rw [hw]; exact subset_closure (by simp)
      · rw [hw]; exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · intro t ht
    rcases ht with ht | ht
    · rw [ht]; exact subset_closure (by simp)
    · rw [Set.mem_singleton_iff.1 ht]
      rcases hw with hw | hw
      · rw [← hw]; exact subset_closure (by simp)
      · have : l = z⁻¹ * w := by rw [hw]; group
        rw [this]
        exact mul_mem (inv_mem (subset_closure (by simp))) (subset_closure (by simp))

theorem centralizer_triple_part {z w l v : G} (hw : w = l ∨ w = z * l) :
    centralizer ({z, w, v} : Set G) = centralizer ({z, l, v} : Set G) := by
  apply centralizer_eq_of_generate
  · intro s hs
    rcases hs with hs | hs | hs
    · rw [hs]; exact subset_closure (by simp)
    · rw [hs]
      rcases hw with hw | hw
      · rw [hw]; exact subset_closure (by simp)
      · rw [hw]; exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · rw [Set.mem_singleton_iff.1 hs]; exact subset_closure (by simp)
  · intro t ht
    rcases ht with ht | ht | ht
    · rw [ht]; exact subset_closure (by simp)
    · rw [ht]
      rcases hw with hw | hw
      · rw [← hw]; exact subset_closure (by simp)
      · have : l = z⁻¹ * w := by rw [hw]; group
        rw [this]
        exact mul_mem (inv_mem (subset_closure (by simp))) (subset_closure (by simp))
    · rw [Set.mem_singleton_iff.1 ht]; exact subset_closure (by simp)

end Gen

@[expose] def KNormal {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∀ u : L, orderOf u = 2 → Nat.card (centralizer ({u} : Set L)) = 116480 →
    ∀ d ∈ centralizer ({(u : G)} : Set G), ∀ k ∈ (derivedCentralizer u).map L.subtype,
      d * k * d⁻¹ ∈ (derivedCentralizer u).map L.subtype

section Contra

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

omit [Finite G] in
theorem Config.not_sq (hc : Config G L z) (w : G) : w * w ≠ z := by
  intro hw
  have hwz : w * z = z * w := by
    calc w * z = w * (w * w) := by rw [hw]
      _ = (w * w) * w := by group
      _ = z * w := by rw [hw]
  rcases hc.mem_cases (mem_centralizer_singleton_iff.2 hwz) with h | ⟨l, hl, rfl⟩
  · exact hc.z_not_mem (hw ▸ mul_mem h h)
  · apply hc.z_not_mem
    have hcomm := hc.comm l hl
    have : (z * l) * (z * l) = l * l := by
      calc (z * l) * (z * l) = z * (l * z) * l := by group
        _ = z * (z * l) * l := by rw [hcomm]
        _ = (z * z) * (l * l) := by group
        _ = l * l := by rw [hc.z_sq, one_mul]
    rw [← hw, this]
    exact mul_mem hl hl

omit [Finite G] in
theorem Config.exists_part (hc : Config G L z) {w : G} (hw : w * z = z * w) :
    ∃ l : L, w = (l : G) ∨ w = z * (l : G) := by
  rcases hc.mem_cases (mem_centralizer_singleton_iff.2 hw) with h | ⟨l, hl, rfl⟩
  · exact ⟨⟨w, h⟩, Or.inl rfl⟩
  · exact ⟨⟨l, hl⟩, Or.inr rfl⟩

theorem mem_centralizer_of_mem_derivedCentralizer {Y : Type*} [Group Y] {u k : Y}
    (hk : k ∈ derivedCentralizer u) : k ∈ centralizer ({u} : Set Y) := by
  obtain ⟨c, -, rfl⟩ := hk
  exact c.2

theorem Config.false_of_normal (hc : Config G L z) (hF : RuFacts L) (hN : KNormal L) :
    False := by
  classical
  have hz2 : z * z = 1 := hc.z_sq
  obtain ⟨u, a, hu2, huB, ha2, haA, hau, ha_der, h256⟩ := hF.pair
  have huu : (u : G) * (u : G) = 1 := congrArg Subtype.val (sq_eq_one_of_orderOf_two hu2)
  have haa : (a : G) * (a : G) = 1 := congrArg Subtype.val (sq_eq_one_of_orderOf_two ha2)
  have hzu : (u : G) * z = z * (u : G) := hc.comm u u.2
  have hza : (a : G) * z = z * (a : G) := hc.comm a a.2
  have hau' : (a : G) * (u : G) = (u : G) * (a : G) := congrArg Subtype.val hau
  have hxz : IsConj z (z * (a : G)) := hc.isConj_mul_of_classA hF ha2 haA
  obtain ⟨g, hg⟩ := isConj_iff.1 hxz
  set x : G := z * (a : G) with hx
  have hgz : g * z = x * g := by
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = x * g := by rw [hg]
  have hg1 : g⁻¹ * x * g = z := by
    calc g⁻¹ * x * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hg]
      _ = z := by group
  have hxa : x * (a : G) = z := by
    calc x * (a : G) = z * ((a : G) * a) := by rw [hx]; group
      _ = z := by rw [haa, mul_one]
  have hax : (a : G) * x = z := by
    calc (a : G) * x = ((a : G) * z) * a := by rw [hx]; group
      _ = (z * (a : G)) * a := by rw [hza]
      _ = z := by rw [mul_assoc, haa, mul_one]
  have hxu : x * (u : G) = (u : G) * x := by
    calc x * (u : G) = z * ((a : G) * u) := by rw [hx]; group
      _ = z * ((u : G) * a) := by rw [hau']
      _ = (z * (u : G)) * a := by group
      _ = ((u : G) * z) * a := by rw [hzu]
      _ = (u : G) * x := by rw [hx]; group
  set u' : G := g⁻¹ * (u : G) * g with hu'
  set a' : G := g⁻¹ * (a : G) * g with ha'
  have hu'z : u' * z = z * u' := by
    calc u' * z = g⁻¹ * (u : G) * (g * z) := by rw [hu']; group
      _ = g⁻¹ * (u : G) * (x * g) := by rw [hgz]
      _ = g⁻¹ * ((u : G) * x) * g := by group
      _ = g⁻¹ * (x * (u : G)) * g := by rw [hxu]
      _ = (g⁻¹ * x * g) * (g⁻¹ * (u : G) * g) := by group
      _ = z * u' := by rw [hg1]
  have ha'z : a' * z = z * a' := by
    calc a' * z = g⁻¹ * (a : G) * (g * z) := by rw [ha']; group
      _ = g⁻¹ * (a : G) * (x * g) := by rw [hgz]
      _ = g⁻¹ * ((a : G) * x) * g := by group
      _ = g⁻¹ * (x * (a : G)) * g := by rw [hax, hxa]
      _ = (g⁻¹ * x * g) * (g⁻¹ * (a : G) * g) := by group
      _ = z * a' := by rw [hg1]
  have hgz' : g⁻¹ * z * g = z * a' := by
    calc g⁻¹ * z * g = g⁻¹ * (x * (a : G)) * g := by rw [hxa]
      _ = (g⁻¹ * x * g) * (g⁻¹ * (a : G) * g) := by group
      _ = z * a' := by rw [hg1]
  have hgu' : g * u' * g⁻¹ = (u : G) := by rw [hu']; group
  have hga' : g * a' * g⁻¹ = (a : G) := by rw [ha']; group
  have hu'sq : u' * u' = 1 := by
    calc u' * u' = g⁻¹ * ((u : G) * u) * g := by rw [hu']; group
      _ = 1 := by rw [huu]; group
  have ha'sq : a' * a' = 1 := by
    calc a' * a' = g⁻¹ * ((a : G) * a) * g := by rw [ha']; group
      _ = 1 := by rw [haa]; group
  obtain ⟨ℓ, hℓ⟩ := hc.exists_part hu'z
  have hℓsq : (ℓ : G) * (ℓ : G) = 1 := by
    rcases hℓ with h | h
    · rw [h] at hu'sq; exact hu'sq
    · rw [h] at hu'sq
      have hc' := hc.comm ℓ ℓ.2
      calc (ℓ : G) * ℓ = (z * z) * ((ℓ : G) * ℓ) := by rw [hz2, one_mul]
        _ = z * ((z * (ℓ : G)) * ℓ) := by group
        _ = z * (((ℓ : G) * z) * ℓ) := by rw [hc']
        _ = (z * (ℓ : G)) * (z * (ℓ : G)) := by group
        _ = 1 := hu'sq
  have hℓne : ℓ ≠ 1 := by
    intro h1
    have h1' : (ℓ : G) = 1 := by rw [h1]; rfl
    rcases hℓ with h | h
    · have hu1 : (u : G) = 1 := by
        calc (u : G) = g * u' * g⁻¹ := hgu'.symm
          _ = 1 := by rw [h, h1']; group
      have : u = 1 := Subtype.ext hu1
      rw [this, orderOf_one] at hu2
      omega
    · have hu1 : (u : G) = z * (a : G) := by
        calc (u : G) = g * u' * g⁻¹ := hgu'.symm
          _ = g * z * g⁻¹ := by rw [h, h1', mul_one]
          _ = x := hg
      apply hc.z_not_mem
      have : z = (u : G) * ((a : G))⁻¹ := by rw [hu1]; group
      rw [this]
      exact mul_mem u.2 (inv_mem a.2)
  have hℓ2 : orderOf ℓ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hℓsq) hℓne
  have hcardD' : Nat.card (centralizer ({x, (u : G)} : Set G)) =
      2 * Nat.card (centralizer ({ℓ} : Set L)) := by
    have himg : (fun s : G => g * s * g⁻¹) '' ({z, u'} : Set G) = {x, (u : G)} := by
      rw [Set.image_pair, hg, hgu']
    rw [← himg, card_centralizer_conj_image g {z, u'}, centralizer_pair_part hℓ]
    exact hc.card_centralizer_pair ℓ
  rcases hF.card_centralizer ℓ hℓ2 with hA | hB
  ·
    obtain ⟨m, hm⟩ := hc.exists_part ha'z
    have hcardz' : Nat.card (centralizer ({z, z * a'} : Set G)) =
        2 * Nat.card (centralizer ({a} : Set L)) := by
      have himg : (fun s : G => g⁻¹ * s * g⁻¹⁻¹) '' ({x, z} : Set G) = {z, z * a'} := by
        rw [Set.image_pair]
        simp only [inv_inv]
        rw [hg1, hgz']
      rw [← himg, card_centralizer_conj_image g⁻¹ {x, z}, Set.pair_comm,
        centralizer_pair_part (z := z) (w := x) (l := (a : G)) (Or.inr hx)]
      exact hc.card_centralizer_pair a
    have hmsq : (m : G) * (m : G) = 1 := by
      rcases hm with h | h
      · rw [h] at ha'sq; exact ha'sq
      · rw [h] at ha'sq
        have hc' := hc.comm m m.2
        calc (m : G) * m = (z * z) * ((m : G) * m) := by rw [hz2, one_mul]
          _ = z * ((z * (m : G)) * m) := by group
          _ = z * (((m : G) * z) * m) := by rw [hc']
          _ = (z * (m : G)) * (z * (m : G)) := by group
          _ = 1 := ha'sq
    have hmA : Nat.card (centralizer ({m} : Set L)) = 245760 := by
      have h1 : centralizer ({z, z * a'} : Set G) = centralizer ({z, (m : G)} : Set G) := by
        rw [centralizer_pair_part (z := z) (w := z * a') (l := a') (Or.inr rfl),
          centralizer_pair_part hm]
      rw [h1, hc.card_centralizer_pair m, haA] at hcardz'
      omega
    have hm1 : m ≠ 1 := by
      intro h1
      have h1' : (m : G) = 1 := by rw [h1]; rfl
      rcases hm with h | h
      · have : (a : G) = 1 := by
          calc (a : G) = g * a' * g⁻¹ := hga'.symm
            _ = 1 := by rw [h, h1']; group
        have : a = 1 := Subtype.ext this
        rw [this, orderOf_one] at ha2
        omega
      · have hax' : (a : G) = z * (a : G) := by
          calc (a : G) = g * a' * g⁻¹ := hga'.symm
            _ = g * z * g⁻¹ := by rw [h, h1', mul_one]
            _ = x := hg
        apply hc.z_not_mem
        have : z = (a : G) * ((a : G))⁻¹ * z := by group
        have h3 : z * (a : G) = (a : G) := hax'.symm
        have : z = (a : G) * ((a : G))⁻¹ := by
          calc z = (z * (a : G)) * ((a : G))⁻¹ := by group
            _ = (a : G) * ((a : G))⁻¹ := by rw [h3]
        rw [this]
        exact mul_mem a.2 (inv_mem a.2)
    have hm2 : orderOf m = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hmsq) hm1
    have ha'm : a' = (m : G) := by
      rcases hm with h | h
      · exact h
      · exfalso
        have hzm : z * a' = (m : G) := by
          rw [h]
          calc z * (z * (m : G)) = (z * z) * (m : G) := by group
            _ = m := by rw [hz2, one_mul]
        obtain ⟨y, hy⟩ := hF.sq_A m hm2 hmA
        have hy' : (y : G) * (y : G) = (m : G) := by
          have := congrArg Subtype.val hy
          simpa [pow_two] using this
        refine hc.not_sq (g * (y : G) * g⁻¹) ?_
        calc g * (y : G) * g⁻¹ * (g * (y : G) * g⁻¹) = g * ((y : G) * y) * g⁻¹ := by group
          _ = g * (m : G) * g⁻¹ := by rw [hy']
          _ = g * (z * a') * g⁻¹ := by rw [hzm]
          _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz']
          _ = z := by group
    have hℓm : (ℓ : L) * m = m * ℓ := by
      apply Subtype.ext
      show (ℓ : G) * (m : G) = (m : G) * (ℓ : G)
      have h0 : u' * a' = a' * u' := by
        calc u' * a' = g⁻¹ * ((u : G) * a) * g := by rw [hu', ha']; group
          _ = g⁻¹ * ((a : G) * u) * g := by rw [hau']
          _ = a' * u' := by rw [hu', ha']; group
      rw [ha'm] at h0
      have hcm := hc.comm m m.2
      rcases hℓ with h | h
      · rw [h] at h0; exact h0
      · rw [h] at h0
        apply mul_left_cancel (a := z)
        calc z * ((ℓ : G) * m) = (z * (ℓ : G)) * m := by group
          _ = (m : G) * (z * (ℓ : G)) := h0
          _ = ((m : G) * z) * ℓ := by group
          _ = (z * (m : G)) * ℓ := by rw [hcm]
          _ = z * ((m : G) * ℓ) := by group
    have hne : ℓ ≠ m := by
      intro hlm
      rcases hℓ with h | h
      · have h3 : u' = a' := by rw [h, hlm, ha'm]
        have hua : (u : G) = (a : G) := by
          calc (u : G) = g * u' * g⁻¹ := hgu'.symm
            _ = g * a' * g⁻¹ := by rw [h3]
            _ = a := hga'
        have : u = a := Subtype.ext hua
        rw [this] at huB
        rw [huB] at haA
        norm_num at haA
      · have h3 : u' = z * a' := by rw [h, hlm, ha'm]
        have hzu' : (u : G) = z := by
          calc (u : G) = g * u' * g⁻¹ := hgu'.symm
            _ = g * (z * a') * g⁻¹ := by rw [h3]
            _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz']
            _ = z := by group
        exact hc.z_not_mem (hzu' ▸ u.2)
    have hcard3 : Nat.card (centralizer ({z, (ℓ : G), (m : G)} : Set G)) =
        Nat.card (centralizer ({z, (a : G), (u : G)} : Set G)) := by
      have himg : (fun s : G => g⁻¹ * s * g⁻¹⁻¹) '' ({x, z, (u : G)} : Set G) =
          {z, z * a', u'} := by
        rw [Set.image_insert_eq, Set.image_pair]
        simp only [inv_inv]
        rw [hg1, hgz']
      have h1 := card_centralizer_conj_image g⁻¹ ({x, z, (u : G)} : Set G)
      rw [himg] at h1
      have h2 : centralizer ({z, z * a', u'} : Set G) =
          centralizer ({z, (ℓ : G), (m : G)} : Set G) := by
        rw [centralizer_triple_part (z := z) (w := z * a') (l := a') (v := u') (Or.inr rfl), ha'm,
          Set.pair_comm (m : G) u', centralizer_triple_part hℓ]
      have h3 : centralizer ({x, z, (u : G)} : Set G) =
          centralizer ({z, (a : G), (u : G)} : Set G) := by
        apply centralizer_eq_of_generate
        · intro s hs
          rcases hs with hs | hs | hs
          · rw [hs, hx]
            exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
          · rw [hs]; exact subset_closure (by simp)
          · rw [Set.mem_singleton_iff.1 hs]; exact subset_closure (by simp)
        · intro t ht
          rcases ht with ht | ht | ht
          · rw [ht]; exact subset_closure (by simp)
          · rw [ht]
            have : (a : G) = z⁻¹ * x := by rw [hx]; group
            rw [this]
            exact mul_mem (inv_mem (subset_closure (by simp))) (subset_closure (by simp))
          · rw [Set.mem_singleton_iff.1 ht]; exact subset_closure (by simp)
      rw [← h2, h1, h3]
    rw [hc.card_centralizer_triple ℓ m, hc.card_centralizer_triple a u, h256] at hcard3
    exact hF.no_256 ℓ m hℓ2 hm2 hne hℓm hA hmA (by omega)
  ·
    have h13 : 13 ∣ Nat.card (centralizer ({x, (u : G)} : Set G)) := by
      rw [hcardD', hB]; norm_num
    have : Fact (Nat.Prime 13) := ⟨by decide⟩
    obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card'
      (G := centralizer ({x, (u : G)} : Set G)) 13 h13
    have hf13 : orderOf (f : G) = 13 := by rw [Subgroup.orderOf_coe]; exact hf
    have hfx : x * (f : G) = (f : G) * x := mem_centralizer_iff.1 f.2 x (by simp)
    have hfu : (u : G) * (f : G) = (f : G) * (u : G) := mem_centralizer_iff.1 f.2 u (by simp)
    set K : Subgroup G := (derivedCentralizer u).map L.subtype with hK
    set R : Subgroup G := K ⊓ centralizer ({x} : Set G) with hR
    have hfmem : (f : G) ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hfx.symm
    have hnorm : ∀ r ∈ R, (f : G) * r * (f : G)⁻¹ ∈ R := by
      intro r hr
      have h1 := hN u hu2 huB (f : G) (mem_centralizer_singleton_iff.2 hfu.symm) r hr.1
      have h2 : (f : G) * r * (f : G)⁻¹ ∈ centralizer ({x} : Set G) :=
        mul_mem (mul_mem hfmem hr.2) (inv_mem hfmem)
      exact Subgroup.mem_inf.2 ⟨h1, h2⟩
    have haK : (a : G) ∈ K := Subgroup.mem_map.2 ⟨a, ha_der, rfl⟩
    have haR : (a : G) ∈ R :=
      Subgroup.mem_inf.2 ⟨haK, mem_centralizer_singleton_iff.2 (by rw [hxa, hax])⟩
    have hRle : R ≤ (centralizer ({a} : Set L) ⊓ centralizer ({u} : Set L)).map L.subtype := by
      intro r hr
      obtain ⟨k, hk, rfl⟩ := (Subgroup.mem_inf.1 hr).1
      refine ⟨k, Subgroup.mem_inf.2 ⟨?_, mem_centralizer_of_mem_derivedCentralizer hk⟩, rfl⟩
      have h1 : (L.subtype k : G) * x = x * (L.subtype k : G) :=
        mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hr).2
      have hkz : (k : G) * z = z * (k : G) := hc.comm k k.2
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      show (k : G) * (a : G) = (a : G) * (k : G)
      apply mul_left_cancel (a := z)
      calc z * ((k : G) * a) = (z * (k : G)) * a := by group
        _ = ((k : G) * z) * a := by rw [hkz]
        _ = (k : G) * x := by rw [hx]; group
        _ = x * (k : G) := h1
        _ = z * ((a : G) * k) := by rw [hx]; group
    have hRcard : Nat.card R ∣ 256 := by
      have := Subgroup.card_dvd_of_le hRle
      rwa [Subgroup.card_map_of_injective L.subtype_injective, h256] at this
    have hcomm := commute_of_normalizing_order_thirteen hf13 hnorm hRcard
    have hfa : (f : G) * (a : G) = (a : G) * (f : G) := hcomm _ haR
    have hfz : (f : G) * z = z * (f : G) := by
      calc (f : G) * z = (f : G) * (x * (a : G)) := by rw [hxa]
        _ = ((f : G) * x) * a := by group
        _ = (x * (f : G)) * a := by rw [hfx]
        _ = x * ((f : G) * a) := by group
        _ = x * ((a : G) * f) := by rw [hfa]
        _ = (x * (a : G)) * f := by group
        _ = z * (f : G) := by rw [hxa]
    have hmem : (f : G) ∈ centralizer ({z, (a : G), (u : G)} : Set G) := by
      rw [mem_centralizer_iff]
      intro t ht
      rcases ht with ht | ht | ht
      · rw [ht]; exact hfz.symm
      · rw [ht]; exact hfa.symm
      · rw [Set.mem_singleton_iff.1 ht]; exact hfu
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hf13, hc.card_centralizer_triple a u, h256] at hdvd
    norm_num at hdvd

end Contra

end CFSG.EvenSporadicStandard.RuStd

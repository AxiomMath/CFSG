module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineRankBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineCountCentral
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineCountRank
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineCountLift
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineCountSection
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineCountGroup

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools SixNineCount

theorem rankCountInput_holds : SixNineRank.RankCountInput := by
  intro G _ _ N U R X K t v y ε hRX hXU hUK hKN hNU hNR hNK hsq hcomm hsyl ht hv ht2 hv2 htv
    htn hvn htvn hy hyt hyv hconj hk hCK hCX hεN hεt hεp hεfree hirr
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRU : R ≤ U := hRX.trans hXU
  have hUN : U ≤ N := hUK.trans hKN
  have hfact : Fact (SecHyp U R) := ⟨⟨hRU, fun u hu r hr =>
    (mem_normalizer_iff.mp (hNR (hUN hu)) r).mp hr, hcomm, hsq⟩⟩
  set ρ := secRep N hNU hNR with hρdef
  have hρ1 : ∀ g : N, ρ g = 1 ↔ ∀ a ∈ U, (g : G) * a * (g : G)⁻¹ * a⁻¹ ∈ R :=
    fun g => secRep_eq_one_iff g
  have hρU : ∀ g : N, (g : G) ∈ U → ρ g = 1 := fun g hg =>
    (hρ1 g).mpr fun a ha => hcomm _ hg a ha
  have hρD : ∀ g : G, (hg : g ∈ secKer N U R hNU hNR) → ρ ⟨g, hg.1⟩ = 1 := fun g hg =>
    (hρ1 ⟨g, hg.1⟩).mpr hg.2
  have hDρ : ∀ g : N, ρ g = 1 → (g : G) ∈ secKer N U R hNU hNR := fun g hg =>
    ⟨g.2, (hρ1 g).mp hg⟩
  set tN : N := ⟨t, ht⟩ with htN
  set vN : N := ⟨v, hv⟩ with hvN
  set yN : N := ⟨y, hy⟩ with hyN
  set εN : N := ⟨ε, hεN⟩ with hεNdef
  set tb := ρ tN with htb
  set vb := ρ vN with hvb
  set yb := ρ yN with hyb
  set εb := ρ εN with hεb
  have htb2 : tb * tb = 1 := by
    rw [htb, ← map_mul, show tN * tN = 1 from Subtype.ext (by
      change t * t = 1; rw [← pow_two, ht2]), map_one]
  have hvb2 : vb * vb = 1 := by
    rw [hvb, ← map_mul, show vN * vN = 1 from Subtype.ext (by
      change v * v = 1; rw [← pow_two, hv2]), map_one]
  have htvb : tb * vb = vb * tb := by
    rw [htb, hvb, ← map_mul, ← map_mul, show tN * vN = vN * tN from Subtype.ext htv]
  have hyb_t : yb⁻¹ * tb * yb = vb := by
    have h1 : ρ (vN⁻¹ * (yN⁻¹ * tN * yN)) = 1 := hρU _ hyt
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (inv_mul_eq_one.mp h1).symm
  have hyb_v : yb⁻¹ * vb * yb = tb * vb := by
    have h1 : ρ ((tN * vN)⁻¹ * (yN⁻¹ * vN * yN)) = 1 := hρU _ hyv
    rw [map_mul, map_inv, map_mul, map_mul, map_mul, map_inv] at h1
    exact (inv_mul_eq_one.mp h1).symm
  have : Finite (AddMonoid.End (Sec U R)) :=
    Finite.of_injective (fun f : AddMonoid.End (Sec U R) => (f : Sec U R → Sec U R))
      (fun f g h => AddMonoidHom.ext (congrFun h))
  have : Finite (AddMonoid.End (Sec U R))ˣ := Finite.of_injective Units.val Units.val_injective
  set ρK : K →* (AddMonoid.End (Sec U R))ˣ := ρ.comp (Subgroup.inclusion hKN) with hρK
  set Kb := ρK.range with hKb
  have hKbodd : Odd (Nat.card Kb) := by
    have h1 : U.subgroupOf K ≤ ρK.ker := fun u hu => by
      rw [MonoidHom.mem_ker]
      exact hρU _ hu
    have h3 : ρK.ker.index ∣ (U.subgroupOf K).index := Subgroup.index_dvd_of_le h1
    have h4 : ¬ 2 ∣ (U.subgroupOf K).index := (isSylowOf_iff.mp hsyl).2.2
    rw [← Subgroup.index_ker ρK]
    rcases Nat.even_or_odd ρK.ker.index with h | h
    · exact absurd ((even_iff_two_dvd.mp h).trans h3) h4
    · exact h
  set Nb := ρ.range with hNb
  have hmemNb : ∀ g : N, ρ g ∈ Nb := fun g => ⟨g, rfl⟩
  have hconjNb : ∀ g ∈ Nb, ∀ k ∈ Kb, g * k * g⁻¹ ∈ Kb := by
    rintro _ ⟨n, rfl⟩ _ ⟨k, rfl⟩
    have hmem : (n : G) * k * (n : G)⁻¹ ∈ K := (mem_normalizer_iff.mp (hNK n.2) k).mp k.2
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [hρK, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hKbne : Kb ≠ ⊥ := by
    obtain ⟨k, hkK, hkn⟩ := hk
    intro hbot
    have hmem : ρK ⟨k, hkK⟩ ∈ Kb := ⟨_, rfl⟩
    rw [hbot, mem_bot] at hmem
    exact hkn ((hρ1 _).mp hmem)
  obtain ⟨Hb, hHbKb, ⟨hHbne, hHbconj⟩, hHbmin⟩ := exists_minimal_subgroup
    (fun H : Subgroup (AddMonoid.End (Sec U R))ˣ => H ≠ ⊥ ∧ ∀ g ∈ Nb, ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (H₀ := Kb) ⟨hKbne, hconjNb⟩
  have hHbodd : Odd (Nat.card Hb) := hKbodd.of_dvd_nat (Subgroup.card_dvd_of_le hHbKb)
  obtain ⟨hHcomm, l, hl, hl2, hHexp⟩ := abelian_exponent_of_minimal (S := Nb) hHbodd hHbne
    hHbconj (fun H' hle hne hconj' => hHbmin H' hle ⟨hne, hconj'⟩)
  have htH : ∀ h ∈ Hb, tb * h * tb⁻¹ ∈ Hb := hHbconj _ (hmemNb tN)
  have hvH : ∀ h ∈ Hb, vb * h * vb⁻¹ ∈ Hb := hHbconj _ (hmemNb vN)
  have hyH : ∀ h ∈ Hb, yb * h * yb⁻¹ ∈ Hb := hHbconj _ (hmemNb yN)
  have hyH' : ∀ h ∈ Hb, yb⁻¹ * h * yb ∈ Hb := fun h hh => by
    have h1 := hHbconj _ (Nb.inv_mem (hmemNb yN)) h hh
    rwa [inv_inv] at h1
  have hεH : ∀ h ∈ Hb, εb * h * εb⁻¹ ∈ Hb := hHbconj _ (hmemNb εN)
  have hlift : ∀ h ∈ Hb, h * tb = tb * h → ∃ x : G, ∃ hxK : x ∈ K, x * t = t * x ∧
      Odd (orderOf x) ∧ ρ ⟨x, hKN hxK⟩ = h := by
    intro h hh hht
    obtain ⟨k, rfl⟩ := hHbKb hh
    have hxt : (k : G) * t * (k : G)⁻¹ * t⁻¹ ∈ secKer N U R hNU hNR := by
      have h1 := hDρ (Subgroup.inclusion hKN k * tN * (Subgroup.inclusion hKN k)⁻¹ * tN⁻¹) (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        change ρK k * tb * (ρK k)⁻¹ * tb⁻¹ = 1
        rw [hht]; group)
      exact h1
    have hmodd : Odd (orderOf (ρK k)) :=
      hKbodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Kb ⟨k, rfl⟩)
    have hxm : (k : G) ^ orderOf (ρK k) ∈ secKer N U R hNU hNR := by
      have h1 := hDρ (Subgroup.inclusion hKN k ^ orderOf (ρK k)) (by
        rw [map_pow]
        exact pow_orderOf_eq_one (ρK k))
      exact h1
    obtain ⟨x', hx'K, hx't, hx'odd, hx'D⟩ :=
      exists_comm_lift_odd hUK hKN hNU hNR hNK hcomm hsyl ht ht2 hconj k.2 hxt hmodd hxm
    refine ⟨x', hx'K, hx't, hx'odd, ?_⟩
    have h1 := hρD _ hx'D
    rw [show (⟨x'⁻¹ * k, hx'D.1⟩ : N) = (⟨x', hKN hx'K⟩ : N)⁻¹ * Subgroup.inclusion hKN k from
      Subtype.ext rfl, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hCW : ∀ h ∈ Hb, h * tb = tb * h → h * vb = vb * h → h = 1 := by
    intro h hh hht hhv
    obtain ⟨x, hxK, hxt, hxodd, hxh⟩ := hlift h hh hht
    have hxv : ∀ a ∈ U, x * v * x⁻¹ * v⁻¹ * a * (x * v * x⁻¹ * v⁻¹)⁻¹ * a⁻¹ ∈ R := by
      have h1 := (hρ1 ((⟨x, hKN hxK⟩ : N) * vN * (⟨x, hKN hxK⟩ : N)⁻¹ * vN⁻¹)).mp (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxh]
        show h * vb * h⁻¹ * vb⁻¹ = 1
        rw [hhv]; group)
      exact h1
    have h2 := hCK x hxK hxt hxodd hxv
    rw [← hxh]
    exact (hρ1 _).mpr h2
  obtain ⟨x₁, hx₁H, hx₁ne, hx₁t⟩ :=
    exists_ne_one_comm hHcomm hHbne htb2 hvb2 htH hvH hyH hyb_t hyb_v
  obtain ⟨x₂, hx₂⟩ : ∃ x₂, x₂ = yb⁻¹ * x₁ * yb := ⟨_, rfl⟩
  obtain ⟨x₃, hx₃⟩ : ∃ x₃, x₃ = yb⁻¹ * x₂ * yb := ⟨_, rfl⟩
  have hx₂H : x₂ ∈ Hb := by rw [hx₂]; exact hyH' x₁ hx₁H
  have hx₃H : x₃ ∈ Hb := by rw [hx₃]; exact hyH' x₂ hx₂H
  have hx₂v : x₂ * vb = vb * x₂ := by
    rw [hx₂, ← hyb_t]
    calc yb⁻¹ * x₁ * yb * (yb⁻¹ * tb * yb) = yb⁻¹ * (x₁ * tb) * yb := by group
      _ = yb⁻¹ * (tb * x₁) * yb := by rw [hx₁t]
      _ = yb⁻¹ * tb * yb * (yb⁻¹ * x₁ * yb) := by group
  have hx₃tv : x₃ * (tb * vb) = (tb * vb) * x₃ := by
    rw [hx₃, ← hyb_v]
    calc yb⁻¹ * x₂ * yb * (yb⁻¹ * vb * yb) = yb⁻¹ * (x₂ * vb) * yb := by group
      _ = yb⁻¹ * (vb * x₂) * yb := by rw [hx₂v]
      _ = yb⁻¹ * vb * yb * (yb⁻¹ * x₂ * yb) := by group
  have hconj_ne : ∀ a : (AddMonoid.End (Sec U R))ˣ, a ≠ 1 → yb⁻¹ * a * yb ≠ 1 := by
    intro a ha h
    apply ha
    calc a = yb * (yb⁻¹ * a * yb) * yb⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hx₂ne : x₂ ≠ 1 := by rw [hx₂]; exact hconj_ne x₁ hx₁ne
  have hx₃ne : x₃ ≠ 1 := by rw [hx₃]; exact hconj_ne x₂ hx₂ne
  have hFl : Fact l.Prime := ⟨hl⟩
  have hord : ∀ x ∈ Hb, x ≠ 1 → orderOf x = l := fun x hx hx1 =>
    orderOf_eq_prime (hHexp x hx) hx1
  have hfree_t : ∀ h ∈ Hb, h * tb = tb * h → h * (tb * vb) = (tb * vb) * h → h = 1 := by
    intro h hh h1 h2
    apply hCW h hh h1
    apply mul_left_cancel (a := tb)
    calc tb * (h * vb) = (tb * h) * vb := by group
      _ = (h * tb) * vb := by rw [h1]
      _ = h * (tb * vb) := by group
      _ = (tb * vb) * h := h2
      _ = tb * (vb * h) := by group
  have hfree_v : ∀ h ∈ Hb, h * vb = vb * h → h * (tb * vb) = (tb * vb) * h → h = 1 := by
    intro h hh h1 h2
    apply hCW h hh _ h1
    apply mul_right_cancel (b := vb)
    calc h * tb * vb = h * (tb * vb) := by group
      _ = (tb * vb) * h := h2
      _ = tb * (vb * h) := by group
      _ = tb * (h * vb) := by rw [h1]
      _ = tb * h * vb := by group
  have htsw : tb * (tb * vb) = (tb * vb) * tb := by
    calc tb * (tb * vb) = tb * (vb * tb) := by rw [htvb]
      _ = tb * vb * tb := (mul_assoc _ _ _).symm
  have hvsw : vb * (tb * vb) = (tb * vb) * vb := by
    calc vb * (tb * vb) = (vb * tb) * vb := by group
      _ = (tb * vb) * vb := by rw [htvb]
  have hti2 : tb * x₂ * tb⁻¹ = x₂⁻¹ :=
    conj_eq_inv_of_comm hHcomm htb2 htH htvb hCW hx₂H hx₂v
  have hti3 : tb * x₃ * tb⁻¹ = x₃⁻¹ :=
    conj_eq_inv_of_comm hHcomm htb2 htH htsw hfree_t hx₃H hx₃tv
  have hvi1 : vb * x₁ * vb⁻¹ = x₁⁻¹ :=
    conj_eq_inv_of_comm hHcomm hvb2 hvH htvb.symm (fun h hh h1 h2 => hCW h hh h2 h1) hx₁H hx₁t
  have hvi3 : vb * x₃ * vb⁻¹ = x₃⁻¹ :=
    conj_eq_inv_of_comm hHcomm hvb2 hvH hvsw hfree_v hx₃H hx₃tv
  have htf1 : tb * x₁ * tb⁻¹ = x₁ := by rw [← hx₁t]; group
  have hvf2 : vb * x₂ * vb⁻¹ = x₂ := by rw [← hx₂v]; group
  let _ : CommGroup Hb :=
    { (inferInstance : Group Hb) with mul_comm := fun a b => Subtype.ext (hHcomm _ a.2 _ b.2) }
  let σ : Hb →* Hb :=
    { toFun := fun h => ⟨tb * h * tb⁻¹, htH h h.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  let τ : Hb →* Hb :=
    { toFun := fun h => ⟨vb * h * vb⁻¹, hvH h h.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hindH := indep_of_inv (C := Hb) (x₁ := ⟨x₁, hx₁H⟩) (x₂ := ⟨x₂, hx₂H⟩)
    (x₃ := ⟨x₃, hx₃H⟩) hl hl2 (by rw [← Subgroup.orderOf_coe]; exact hord _ hx₁H hx₁ne)
    (by rw [← Subgroup.orderOf_coe]; exact hord _ hx₂H hx₂ne)
    (by rw [← Subgroup.orderOf_coe]; exact hord _ hx₃H hx₃ne) σ τ
    (Subtype.ext htf1) (Subtype.ext hti2) (Subtype.ext hti3)
    (Subtype.ext hvi1) (Subtype.ext hvf2) (Subtype.ext hvi3)
  have hind : ∀ α β γ : ℕ, x₁ ^ α * x₂ ^ β * x₃ ^ γ = 1 → l ∣ α ∧ l ∣ β ∧ l ∣ γ :=
    fun α β γ h => hindH α β γ (Subtype.ext h)
  have hεp1 : εb ^ orderOf ε = 1 := by
    rw [hεb, ← map_pow, show εN ^ orderOf ε = 1 from Subtype.ext (by
      change ε ^ orderOf ε = 1; exact pow_orderOf_eq_one ε), map_one]
  have hεsum : ∑ i ∈ Finset.range (orderOf ε), ((εb : AddMonoid.End (Sec U R))) ^ i = 0 := by
    have hpow' : (εb : AddMonoid.End (Sec U R)) ^ orderOf ε = 1 := by
      rw [← Units.val_pow_eq_pow_val, hεp1, Units.val_one]
    have hfix := mul_geom_sum_eq_of_pow_eq_one hpow'
    ext w
    have h1 := fixed_eq_zero_of_free (hNU := hNU) (hNR := hNR) εN hεfree
      ((∑ i ∈ Finset.range (orderOf ε), (εb : AddMonoid.End (Sec U R)) ^ i) w)
      (by
        change ((εb : AddMonoid.End (Sec U R)) *
          ∑ i ∈ Finset.range (orderOf ε), (εb : AddMonoid.End (Sec U R)) ^ i) w = _
        rw [hfix])
    rw [h1]
    rfl
  have hεcomm : ∀ a ∈ Hb, εb * a = a * εb :=
    commute_of_geom_sum_eq_zero (two_eq_zero_end Sec.add_self) Hb hHcomm hl hl2 hHexp hεp hεp1
      hεH hεsum
  obtain ⟨x, hxK, hxt, hxodd, hxh⟩ := hlift x₁ hx₁H hx₁t
  set xN : N := ⟨x, hKN hxK⟩ with hxNdef
  have hxnt : ¬ ∀ a ∈ U, x * a * x⁻¹ * a⁻¹ ∈ R := fun h =>
    hx₁ne (by rw [← hxh]; exact (hρ1 _).mpr h)
  have hxε : ∀ a ∈ U, x * ε * x⁻¹ * ε⁻¹ * a * (x * ε * x⁻¹ * ε⁻¹)⁻¹ * a⁻¹ ∈ R := by
    have h1 := (hρ1 (xN * εN * xN⁻¹ * εN⁻¹)).mp (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxh]
      show x₁ * εb * x₁⁻¹ * εb⁻¹ = 1
      rw [← hεcomm x₁ hx₁H]; group)
    exact h1
  obtain ⟨hlow, hhigh⟩ := hirr x hxK hxt hxodd hxnt hxε
  set B := Subgroup.closure ((Hb : Set (AddMonoid.End (Sec U R))ˣ) ∪ {εb}) with hB
  have hBcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := closure_comm (by
    rintro a (ha | ha) b (hb | hb)
    · exact hHcomm a ha b hb
    · rw [Set.mem_singleton_iff.mp hb]; exact (hεcomm a ha).symm
    · rw [Set.mem_singleton_iff.mp ha]; exact hεcomm b hb
    · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb])
  have hHB : Hb ≤ B := fun h hh => subset_closure (Or.inl hh)
  have hεB : εb ∈ B := subset_closure (Or.inr rfl)
  have hSB : ({ρ εN, ρ xN, (ρ εN)⁻¹, (ρ xN)⁻¹} : Set (AddMonoid.End (Sec U R))ˣ) ⊆ B := by
    intro g hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hεB
    · rw [hxh]; exact hHB hx₁H
    · exact B.inv_mem hεB
    · rw [hxh]; exact B.inv_mem (hHB hx₁H)
  have hεX : ε ∈ normalizer (X : Set G) := hCX ε hεN hεt
  have hxX : x ∈ normalizer (X : Set G) := hCX x (hKN hxK) hxt
  have hX : ∀ g ∈ ({ρ εN, ρ xN, (ρ εN)⁻¹, (ρ xN)⁻¹} : Set (AddMonoid.End (Sec U R))ˣ),
      ∀ w ∈ (secImg X : AddSubgroup (Sec U R)), (g : AddMonoid.End (Sec U R)) w ∈ secImg X := by
    intro g hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact secImg_invariant εN hεX
    · exact secImg_invariant xN hxX
    · rw [← map_inv]; exact secImg_invariant εN⁻¹ ((normalizer _).inv_mem hεX)
    · rw [← map_inv]; exact secImg_invariant xN⁻¹ ((normalizer _).inv_mem hxX)
  have hX₁ := irr_low_transfer (hNU := hNU) (hNR := hNR) hRX εN xN hlow
  have hX₂ := irr_high_transfer (hNU := hNU) (hNR := hNR) hXU εN xN hhigh
  exact false_of_layers_indep Sec.add_self hBcomm hSB hX hX₁ hX₂ hl hl2 (hHB hx₁H) (hHB hx₂H)
    (hHB hx₃H) (hHexp _ hx₁H) (hHexp _ hx₂H) (hHexp _ hx₃H) hind

end CFSG.SeitzReduction.RankOne

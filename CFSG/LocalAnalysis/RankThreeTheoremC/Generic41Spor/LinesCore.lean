module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Fusion
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame41Aux
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (U3Lemma33 u3f_false_of_lines u3f_lines_injOn)

variable {G : Type} [Group G] [Finite G]

@[expose] def conjLinesIn (x : G) (S : Subgroup G) : Set (Subgroup G) :=
  {A | ∃ g : G, A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ S}

theorem map_conj_zpowers (g a : G) :
    (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g * a * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem map_conj_map_conj (g h : G) (A : Subgroup G) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext y
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem map_conj_cancel (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_conj_map_conj]
  ext y
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem map_conj_cancel' (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
  have := map_conj_cancel g⁻¹ A
  rwa [inv_inv] at this

theorem conjLinesIn_normalizer_trans {p : ℕ} [Fact p.Prime] {S : Subgroup G} {x : G}
    (hS : IsSylowOf p S (Subgroup.centralizer ({x} : Set G)))
    (hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ A ∈ conjLinesIn x S, ∃ g ∈ Subgroup.normalizer (S : Set G),
      A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom := by
  rintro A ⟨g', hAg, hAS⟩
  obtain ⟨h, rfl⟩ : ∃ h : G, g' = h⁻¹ := ⟨g'⁻¹, by simp⟩
  have hAy : A = Subgroup.zpowers (h⁻¹ * x * h) := by
    rw [hAg, map_conj_zpowers, inv_inv]
  have hyS : h⁻¹ * x * h ∈ S := hAS (hAy ▸ Subgroup.mem_zpowers _)
  have hB : (S.map (MulAut.conj h).toMonoidHom) ≤ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hss := hSab s hs _ hyS
    show (h * s * h⁻¹) * x = x * (h * s * h⁻¹)
    calc (h * s * h⁻¹) * x = h * (s * (h⁻¹ * x * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * x * h) * s) * h⁻¹ := by rw [hss]
      _ = x * (h * s * h⁻¹) := by group
  have hBp : IsPGroup p (S.map (MulAut.conj h).toMonoidHom) := hS.isPGroup.map _
  obtain ⟨k, hkC, hk⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_conj_le_of_isSylowOf hS hB hBp
  have hkx : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
  have heq : S.map (MulAut.conj (k * h)).toMonoidHom = S := by
    rw [← map_conj_map_conj]
    refine Subgroup.eq_of_le_of_card_ge hk ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective,
      Subgroup.card_map_of_injective (MulAut.conj h).injective]
  have hnorm : k * h ∈ Subgroup.normalizer (S : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  refine ⟨(k * h)⁻¹, Subgroup.inv_mem _ hnorm, ?_⟩
  rw [hAy, map_conj_zpowers]
  congr 1
  calc h⁻¹ * x * h = h⁻¹ * (k⁻¹ * (k * x * k⁻¹) * k) * h := by group
    _ = h⁻¹ * (k⁻¹ * (x * k * k⁻¹) * k) * h := by rw [hkx]
    _ = (k * h)⁻¹ * x * (k * h)⁻¹⁻¹ := by group

theorem lines_core {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {S T Γ : Subgroup G} {x : G}
    (SL : Finset (Subgroup G))
    (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hTS : T ≤ S) (hSC : ∀ s ∈ S, s * x = x * s)
    (hTel : IsElemAbelian p T) (hTcard : Nat.card T = p ^ 2) (hxT : x ∉ T)
    (hΩ : ∀ y ∈ S, y ^ p = 1 → ∃ t ∈ T, ∃ z ∈ Subgroup.zpowers x, y = t * z)
    (hL33 : U3Lemma33 p x)
    (hΓx : ∀ γ ∈ Γ, γ * x = x * γ)
    (hPow : ∀ t ∈ T, t ≠ 1 → ∀ k : ℕ, ¬ p ∣ k → ∃ γ ∈ Γ, γ * t * γ⁻¹ = t ^ k)
    (hSLc : SL.card ≤ 2)
    (htrans : ∀ s ∈ T, ∀ s' ∈ T, s ≠ 1 → s' ≠ 1 → Subgroup.zpowers s ∉ SL →
      Subgroup.zpowers s' ∉ SL → ∃ γ ∈ Γ, γ * s * γ⁻¹ ∈ Subgroup.zpowers s')
    (hNtrans : ∀ A ∈ conjLinesIn x S, ∃ g ∈ Subgroup.normalizer (S : Set G),
      A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom) :
    ∀ A ∈ conjLinesIn x S, A = Subgroup.zpowers x ∨ A ∈ SL := by
  classical
  have hp : p.Prime := Fact.out
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  haveI : IsMulCommutative T := hTel.1
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : T) ⟨b, hb⟩)
  have hΓz : ∀ γ ∈ Γ, ∀ z ∈ Subgroup.zpowers x, γ * z * γ⁻¹ = z := by
    intro γ hγ z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcx : Commute γ x := hΓx γ hγ
    have hc : Commute γ (x ^ k) := hcx.zpow_right k
    calc γ * x ^ k * γ⁻¹ = x ^ k * γ * γ⁻¹ := by rw [hc.eq]
      _ = x ^ k := by group
  have hzgen : ∀ z ∈ Subgroup.zpowers x, z ≠ 1 → Subgroup.zpowers z = Subgroup.zpowers x :=
    fun z hz hz1 => eg41_zpowers_eq_of_mem hp hxo hz hz1
  have hcase : ∀ t ∈ T, t ≠ 1 → ∀ z ∈ Subgroup.zpowers x, z ≠ 1 → ∀ g : G,
      g * x * g⁻¹ = t * z → False := by
    intro t htT ht1 z hzx hz1 g hgy
    have htp : t ^ p = 1 := hTel.2 t htT
    have htx : Commute t x := hSC t (hTS htT)
    have hxt : x ∉ Subgroup.zpowers t := fun h => hxT ((Subgroup.zpowers_le.mpr htT) h)
    obtain ⟨hEel, hEcard⟩ := typeII_zpowers_sup_zpowers hp htp ht1 hxp hx1 htx hxt
    have hEC : Subgroup.zpowers t ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hSC t (hTS htT))
      · rw [Subgroup.mem_centralizer_singleton_iff]
    have hzE : z ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right hzx
    have htE : t ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers x :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    have hzt : z ∉ Subgroup.zpowers t := by
      intro hzt
      apply hxT
      have hxz : x ∈ Subgroup.zpowers z := (hzgen z hzx hz1) ▸ Subgroup.mem_zpowers x
      have hxt' : x ∈ Subgroup.zpowers t := (Subgroup.zpowers_le.mpr hzt) hxz
      exact (Subgroup.zpowers_le.mpr htT) hxt'
    refine u3f_false_of_lines hL33 hEC hEel hEcard hzE htE ht1 hzt (fun i hi => ?_)
    by_cases hi0 : i = 0
    · refine ⟨1, ?_⟩
      rw [hi0, pow_zero, one_mul, map_conj_zpowers, one_mul, inv_one, mul_one]
      exact hzgen z hzx hz1
    · obtain ⟨γ, hγ, hγt⟩ :=
        hPow t htT ht1 i (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi0) hi)
      refine ⟨γ * g, ?_⟩
      rw [map_conj_zpowers]
      congr 1
      calc t ^ i * z = (γ * t * γ⁻¹) * (γ * z * γ⁻¹) := by rw [hγt, hΓz γ hγ z hzx]
        _ = γ * (t * z) * γ⁻¹ := by group
        _ = γ * (g * x * g⁻¹) * γ⁻¹ := by rw [hgy]
        _ = (γ * g) * x * (γ * g)⁻¹ := by group
  have hstep1 : ∀ A ∈ conjLinesIn x S, A ≠ Subgroup.zpowers x → A ≤ T := by
    rintro A ⟨g, hAg, hAS⟩ hAx
    have hAy : A = Subgroup.zpowers (g * x * g⁻¹) := by rw [hAg, map_conj_zpowers]
    have hyS : g * x * g⁻¹ ∈ S := hAS (hAy ▸ Subgroup.mem_zpowers _)
    have hyp : (g * x * g⁻¹) ^ p = 1 := by
      rw [conj_pow, hxp]
      simp
    have hy1 : g * x * g⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [h] at this
      simpa using this
    obtain ⟨t, htT, z, hzx, hyt⟩ := hΩ _ hyS hyp
    by_cases ht1 : t = 1
    · exfalso
      apply hAx
      rw [hAy]
      have hyx : g * x * g⁻¹ ∈ Subgroup.zpowers x := by
        rw [hyt, ht1, one_mul]
        exact hzx
      exact eg41_zpowers_eq_of_mem hp hxo hyx hy1
    · by_cases hz1 : z = 1
      · rw [hAy]
        refine Subgroup.zpowers_le.mpr ?_
        rw [hyt, hz1, mul_one]
        exact htT
      · exact (hcase t htT ht1 z hzx hz1 g hyt).elim
  have hdiag : ∀ t ∈ T, t ≠ 1 → Subgroup.zpowers t ∉ SL →
      Subgroup.zpowers t ∈ conjLinesIn x S → False := by
    intro t htT ht1 htSL htD
    have hto : orderOf t = p := orderOf_eq_prime (hTel.2 t htT) ht1
    obtain ⟨δ, hδN, hδ⟩ := hNtrans _ htD
    obtain ⟨a, haT, hat⟩ : ∃ a ∈ T, a ∉ Subgroup.zpowers t := by
      by_contra hno
      push Not at hno
      have hle : T ≤ Subgroup.zpowers t := fun a ha => hno a ha
      have := Subgroup.card_le_of_le hle
      rw [hTcard, Nat.card_zpowers, hto] at this
      have h2 := hp.two_le
      nlinarith
    have hne : ∀ i : ℕ, t ^ i * a ≠ 1 := by
      intro i h
      apply hat
      have : a = (t ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers t) i)
    have hmem : ∀ i : ℕ, t ^ i * a ∈ T := fun i => T.mul_mem (T.pow_mem htT i) haT
    have hinj := u3f_lines_injOn hTel haT htT ht1 hat
    set lines : Finset (Subgroup G) :=
      (Finset.range p).image (fun i : ℕ => Subgroup.zpowers (t ^ i * a)) with hlines
    have hlinescard : lines.card = p := by
      rw [hlines, Finset.card_image_of_injOn (fun i hi j hj h =>
        hinj (show i < p from Finset.mem_range.mp (Finset.mem_coe.mp hi))
          (show j < p from Finset.mem_range.mp (Finset.mem_coe.mp hj)) h), Finset.card_range]
    set bad : Finset (Subgroup G) := insert (Subgroup.zpowers t) SL with hbad
    have hbadcard : bad.card ≤ 3 := by
      rw [hbad]
      have := Finset.card_insert_le (Subgroup.zpowers t) SL
      omega
    have hgoodcard : 2 ≤ (lines \ bad).card := by
      have := Finset.card_le_card_sdiff_add_card (s := lines) (t := bad)
      omega
    obtain ⟨ℓ₁, hℓ₁, ℓ₂, hℓ₂, hℓ12⟩ := Finset.one_lt_card.mp (by omega : 1 < (lines \ bad).card)
    have hgood : ∀ ℓ ∈ lines \ bad, ∃ s ∈ T, s ≠ 1 ∧ ℓ = Subgroup.zpowers s ∧
        ℓ ∈ conjLinesIn x S ∧ ℓ ≠ Subgroup.zpowers t := by
      intro ℓ hℓ
      obtain ⟨hℓl, hℓb⟩ := Finset.mem_sdiff.mp hℓ
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hℓl
      have hℓt : ℓ ≠ Subgroup.zpowers t := fun h =>
        hℓb (by rw [hbad]; exact Finset.mem_insert.mpr (Or.inl h))
      have hℓSL : ℓ ∉ SL := fun h =>
        hℓb (by rw [hbad]; exact Finset.mem_insert.mpr (Or.inr h))
      refine ⟨t ^ i * a, hmem i, hne i, hi.symm, ?_, hℓt⟩
      have hsSL : Subgroup.zpowers (t ^ i * a) ∉ SL := by rw [hi]; exact hℓSL
      obtain ⟨γ, hγ, hγt⟩ := htrans t htT (t ^ i * a) (hmem i) ht1 (hne i) htSL hsSL
      have hγt1 : γ * t * γ⁻¹ ≠ 1 := by
        intro h
        apply ht1
        have : t = γ⁻¹ * (γ * t * γ⁻¹) * γ := by group
        rw [h] at this
        simpa using this
      have hγto : orderOf (γ * t * γ⁻¹) = p := by
        refine orderOf_eq_prime ?_ hγt1
        rw [conj_pow, hTel.2 t htT]
        simp
      have hseq : Subgroup.zpowers (γ * t * γ⁻¹) = Subgroup.zpowers (t ^ i * a) := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hγt) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, hγto,
          orderOf_eq_prime (hTel.2 _ (hmem i)) (hne i)]
      refine ⟨γ * δ, ?_, ?_⟩
      · rw [← hi, ← hseq, ← map_conj_zpowers, hδ, map_conj_map_conj]
      · rw [← hi]
        exact (Subgroup.zpowers_le.mpr (hmem i)).trans (hTS)
    obtain ⟨s₁, hs₁T, hs₁1, hℓ₁eq, hℓ₁D, hℓ₁t⟩ := hgood ℓ₁ hℓ₁
    obtain ⟨s₂, hs₂T, hs₂1, hℓ₂eq, hℓ₂D, hℓ₂t⟩ := hgood ℓ₂ hℓ₂
    have hδinv : δ⁻¹ ∈ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hδN
    have hconjD : ∀ ℓ ∈ conjLinesIn x S, ℓ ≠ Subgroup.zpowers t →
        ℓ.map (MulAut.conj δ⁻¹).toMonoidHom ≤ T := by
      intro ℓ hℓD hℓt
      obtain ⟨g, hg, hℓS⟩ := hℓD
      have hmemD : ℓ.map (MulAut.conj δ⁻¹).toMonoidHom ∈ conjLinesIn x S := by
        refine ⟨δ⁻¹ * g, ?_, ?_⟩
        · rw [hg, map_conj_map_conj]
        · rintro _ ⟨u, hu, rfl⟩
          have := (Subgroup.mem_normalizer_iff.mp hδinv u).mp (hℓS hu)
          exact this
      have hnex : ℓ.map (MulAut.conj δ⁻¹).toMonoidHom ≠ Subgroup.zpowers x := by
        intro h
        apply hℓt
        have h1 := congrArg (fun B : Subgroup G => B.map (MulAut.conj δ).toMonoidHom) h
        simp only [map_conj_cancel'] at h1
        rw [h1, ← hδ]
      exact hstep1 _ hmemD hnex
    have hℓ₁δ := hconjD ℓ₁ hℓ₁D hℓ₁t
    have hℓ₂δ := hconjD ℓ₂ hℓ₂D hℓ₂t
    rw [hℓ₁eq] at hℓ₁δ
    rw [hℓ₂eq] at hℓ₂δ
    have hs₁p : s₁ ^ p = 1 := hTel.2 s₁ hs₁T
    have hs₂p : s₂ ^ p = 1 := hTel.2 s₂ hs₂T
    have hs₂s₁ : s₂ ∉ Subgroup.zpowers s₁ := by
      intro h
      apply hℓ12
      rw [hℓ₁eq, hℓ₂eq]
      exact (eg41_zpowers_eq_of_mem hp (orderOf_eq_prime hs₁p hs₁1) h hs₂1).symm
    obtain ⟨-, hsupcard⟩ := typeII_zpowers_sup_zpowers hp hs₁p hs₁1 hs₂p hs₂1
      (hTc s₁ hs₁T s₂ hs₂T) hs₂s₁
    have hsupT : Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂ = T :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hs₁T)
        (Subgroup.zpowers_le.mpr hs₂T)) (by rw [hsupcard, hTcard])
    have hTδ : T.map (MulAut.conj δ⁻¹).toMonoidHom ≤ T := by
      have hmapsup := Subgroup.map_sup (Subgroup.zpowers s₁) (Subgroup.zpowers s₂)
        (MulAut.conj δ⁻¹).toMonoidHom
      rw [hsupT] at hmapsup
      rw [hmapsup]
      exact sup_le hℓ₁δ hℓ₂δ
    have hxle : Subgroup.zpowers x ≤ T := by
      have h1 : (Subgroup.zpowers t).map (MulAut.conj δ⁻¹).toMonoidHom = Subgroup.zpowers x := by
        rw [hδ, map_conj_cancel]
      rw [← h1]
      exact (Subgroup.map_mono (Subgroup.zpowers_le.mpr htT)).trans hTδ
    exact hxT (Subgroup.zpowers_le.mp hxle)
  intro A hAD
  by_cases hAx : A = Subgroup.zpowers x
  · exact Or.inl hAx
  · right
    by_contra hASL
    have hAT : A ≤ T := hstep1 A hAD hAx
    obtain ⟨g, hAg, hAS⟩ := hAD
    have hAy : A = Subgroup.zpowers (g * x * g⁻¹) := by rw [hAg, map_conj_zpowers]
    have hyT : g * x * g⁻¹ ∈ T := hAT (hAy ▸ Subgroup.mem_zpowers _)
    have hy1 : g * x * g⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [h] at this
      simpa using this
    exact hdiag _ hyT hy1 (hAy ▸ hASL) (hAy ▸ ⟨g, hAg, hAS⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

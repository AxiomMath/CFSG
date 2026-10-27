module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUInv
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentURho
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsLabels

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem card_centralizer : Nat.card (Subgroup.centralizer (L : Set (QuasiQuotient u))) = 8 := by
  set R := (T : Subgroup (quasiNormalizer u)) ⊓
    (Subgroup.centralizer (L : Set (QuasiQuotient u))).comap (quasiMk u) with hR
  have hmap : R.map (quasiMk u) = Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) fun k hk => ?_
    obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp (d.centralizer_le_sylow hk)
    exact Subgroup.mem_map_of_mem _ ⟨htT, hk⟩
  have hinj : Set.InjOn (quasiMk u) (R : Set (quasiNormalizer u)) := fun a ha b hb hab =>
    quasiMk_injOn_twoGroup u T.isPGroup' ha.1 hb.1 hab
  have h1 : Nat.card (R.map (quasiMk u)) = Nat.card R := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun r : R => (⟨quasiMk u r, Subgroup.mem_map_of_mem _ r.2⟩ : R.map (quasiMk u)))
      ⟨fun a b hab => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab)), ?_⟩)).symm
    rintro ⟨_, ⟨r, hr, rfl⟩⟩
    exact ⟨⟨r, hr⟩, rfl⟩
  have h2 : Nat.card (partCRight T L) = Nat.card R :=
    Subgroup.card_map_of_injective (quasiNormalizer u).subtype_injective
  obtain ⟨φ⟩ := d.caseC3BCD.quaternion_right
  rw [← hmap, h1, ← h2, Nat.card_congr φ.toEquiv, PartC.card_quaternionGroup_two]

theorem card_quasiQuotient : Nat.card (QuasiQuotient u) = 960 := by
  have hker : d.rho5.ker = Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
    ext g
    exact ⟨d.mem_centralizer_of_rho5_eq_one, d.rho5_of_mem_centralizer⟩
  rw [← Subgroup.card_mul_index d.rho5.ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr d.rho5_surjective, Subgroup.card_top, hker, d.card_centralizer,
    Nat.card_eq_fintype_card (α := Perm (Fin 5)), Fintype.card_perm, Fintype.card_fin]
  rfl

theorem exists_conj_eq_forty {w : J ⧸ Subgroup.center J}
    (hwu : Commute w (u : J ⧸ Subgroup.center J)) (hw : CaseC3.Genuine (Subgroup.center J) w)
    (hw1 : w ≠ 1)
    (hwu' : ¬ CaseC3.Genuine (Subgroup.center J) ((u : J ⧸ Subgroup.center J) * w)) :
    ∃ c ∈ Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
      c * w * c⁻¹ = caseC3Word (Subgroup.center J) u m y x 40 := by
  have hu := d.starLift.toEscapingLift
  have hc := d.caseC3BCD.partC
  obtain ⟨g, rfl, hgg⟩ := hw
  have hgX : g ∈ quasiNormalizer u := (hu.mem_quasiNormalizer_iff d.setting).mpr hwu
  have hmk1 : ∀ a : J, (a : J ⧸ Subgroup.center J) = 1 ↔ a = 1 ∨ a = centralElt J := fun a => by
    rw [QuotientGroup.eq_one_iff, d.setting.mem_center_iff]
  have hg1 : g ≠ 1 := fun h => hw1 ((hmk1 g).mpr (Or.inl h))
  have hge : g ≠ centralElt J := fun h => hw1 ((hmk1 g).mpr (Or.inr h))
  have hug : u * g * (u * g) = centralElt J := by
    have hZ : u * g * (u * g) ∈ Subgroup.center J := by
      rw [← QuotientGroup.eq_one_iff]
      have huu : ((u * u : J) : J ⧸ Subgroup.center J) = 1 := (hmk1 _).mpr (Or.inr hc.sq)
      have hgg' : ((g * g : J) : J ⧸ Subgroup.center J) = 1 := (hmk1 _).mpr (Or.inl hgg)
      simp only [QuotientGroup.mk_mul] at huu hgg' ⊢
      calc (u : J ⧸ Subgroup.center J) * g * (u * g) = u * (g * u) * g := by group
        _ = u * (u * g) * g := by rw [hwu.eq]
        _ = u * u * (g * g) := by group
        _ = 1 := by rw [huu, hgg', one_mul]
    rcases d.setting.mem_center_iff.mp hZ with h1 | h1
    · exact absurd ⟨u * g, QuotientGroup.mk_mul _ _ _, h1⟩ hwu'
    · exact h1
  obtain ⟨l₁, hl₁, hl₁l₁, hw₀⟩ :=
    d.exists_eq_quasiBar_mul (w := ⟨g, hgX⟩) (Subtype.ext hgg) hg1 hge hug
  obtain ⟨hvL, hvv⟩ := d.vBar_mem
  obtain ⟨ω, -, c, hc', hω⟩ := d.exists_conj_quasiBar_mul hl₁ hvL hl₁l₁ hvv
  set e₀ : quasiNormalizer u := ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩
  obtain ⟨ε₀, hε₀, hε₀mk⟩ : ∃ ε₀ : quasiNormalizer u,
      ((ε₀ : J) = 1 ∨ (ε₀ : J) = centralElt J) ∧ quasiMk u ε₀ = c := by
    rcases hc' with rfl | rfl
    · exact ⟨1, Or.inl rfl, map_one _⟩
    · exact ⟨e₀, Or.inr rfl, d.quasiMk_centralElt⟩
  obtain ⟨ω₀, rfl⟩ := QuotientGroup.mk_surjective ω
  set v₀ : quasiNormalizer u := ⟨x * u * x⁻¹, d.v_mem⟩
  set t := ω₀ * ⟨g, hgX⟩ * ω₀⁻¹ with ht
  set t' := quasiSelf u * v₀ * ε₀ with ht'
  have hmk : quasiMk u t = quasiMk u t' := by
    simp only [ht, ht', map_mul, map_inv, hε₀mk]
    rw [hw₀]
    exact hω
  have hε₀c : ∀ a : J, a * ε₀ = ε₀ * a := fun a => by
    rcases hε₀ with h3 | h3 <;> rw [h3]
    · group
    · exact (d.setting.commute_centralElt a).eq
  have hε₀ε₀ : (ε₀ : J) * ε₀ = 1 := by
    rcases hε₀ with h3 | h3 <;> rw [h3]
    · group
    · exact d.setting.centralElt_mul_self
  have htt : t * t = 1 := Subtype.ext (by
    simp only [ht, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [show (ω₀ : J) * g * (ω₀ : J)⁻¹ * ((ω₀ : J) * g * (ω₀ : J)⁻¹) =
      ω₀ * (g * g) * (ω₀ : J)⁻¹ by group, hgg]
    group)
  have huv : u * (x * u * x⁻¹) = x * u * x⁻¹ * u :=
    (hc.commute _ d.v_mem_partCLeft u hc.self_mem).symm
  have ht't' : t' * t' = 1 := Subtype.ext (by
    simp only [ht', Subgroup.coe_mul, Subgroup.coe_one]
    change u * (x * u * x⁻¹) * ε₀ * (u * (x * u * x⁻¹) * ε₀) = 1
    rw [show u * (x * u * x⁻¹) * ε₀ * (u * (x * u * x⁻¹) * ε₀) =
        u * (x * u * x⁻¹) * (ε₀ * (u * (x * u * x⁻¹))) * ε₀ by group, ← hε₀c,
      show u * (x * u * x⁻¹) * (u * (x * u * x⁻¹) * ε₀) * ε₀ =
        u * ((x * u * x⁻¹) * u) * (x * u * x⁻¹) * (ε₀ * ε₀) by group, ← huv,
      show u * (u * (x * u * x⁻¹)) * (x * u * x⁻¹) * (ε₀ * ε₀) =
        (u * u) * ((x * u * x⁻¹) * (x * u * x⁻¹)) * (ε₀ * ε₀) by group,
      hc.sq, d.v_mul_self, hc.centralElt_mul_self, hε₀ε₀, one_mul])
  obtain ⟨o, -, hot⟩ := exists_conj_eq_of_inv_mul_mem_odd (quasi_oddCore_odd u) htt ht't'
    (QuotientGroup.eq.mp hmk)
  refine ⟨(((o * ω₀ : quasiNormalizer u) : J) : J ⧸ Subgroup.center J),
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((hu.mem_quasiNormalizer_iff d.setting).mp (o * ω₀).2).eq, ?_⟩
  have hJ : ((o * ω₀ : quasiNormalizer u) : J) * g * ((o * ω₀ : quasiNormalizer u) : J)⁻¹ =
      u * (x * u * x⁻¹) * ε₀ := by
    have := congrArg Subtype.val hot
    simp only [ht, ht', Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
    rw [← this]
    group
  have hε : ((ε₀ : J) : J ⧸ Subgroup.center J) = 1 := by
    rcases hε₀ with h3 | h3 <;> rw [h3]
    · rfl
    · exact (QuotientGroup.eq_one_iff _).mpr d.setting.centralElt_mem_center
  rw [CaseC3BCD.caseC3Word_forty, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, hJ, QuotientGroup.mk_mul, hε, mul_one]

theorem exists_mem_centralizer_conj_eq {s : J ⧸ Subgroup.center J}
    (hs : IsConj (u : J ⧸ Subgroup.center J) s)
    (hsz : Commute s (caseC3Word (Subgroup.center J) u m y x 40))
    (hsz' : ¬ CaseC3.Genuine (Subgroup.center J) (s * caseC3Word (Subgroup.center J) u m y x 40)) :
    ∃ h ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40},
      h * (u : J ⧸ Subgroup.center J) * h⁻¹ = s := by
  set zb := caseC3Word (Subgroup.center J) u m y x 40 with hzb
  obtain ⟨g, hg⟩ := isConj_iff.mp hs
  have hwu : Commute (g⁻¹ * zb * g) (u : J ⧸ Subgroup.center J) := by
    have h1 : (u : J ⧸ Subgroup.center J) = g⁻¹ * s * g := by rw [← hg]; group
    rw [h1]
    calc g⁻¹ * zb * g * (g⁻¹ * s * g) = g⁻¹ * (zb * s) * g := by group
      _ = g⁻¹ * (s * zb) * g := by rw [hsz.eq]
      _ = g⁻¹ * s * g * (g⁻¹ * zb * g) := by group
  have hw : CaseC3.Genuine (Subgroup.center J) (g⁻¹ * zb * g) :=
    CaseC3.genuine_conj _ d.caseC3BCD.genuine_forty g
  have hw1 : g⁻¹ * zb * g ≠ 1 := fun h1 => by
    have h2 : zb = 1 := by
      calc zb = g * (g⁻¹ * zb * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    exact absurd (d.caseC3BCD.caseC3Word_eq_one_iff.mp h2) (by decide)
  have hwu' : ¬ CaseC3.Genuine (Subgroup.center J)
      ((u : J ⧸ Subgroup.center J) * (g⁻¹ * zb * g)) := fun hgen => hsz' (by
    have h1 := CaseC3.genuine_conj _ hgen g⁻¹
    rwa [inv_inv, show g * ((u : J ⧸ Subgroup.center J) * (g⁻¹ * zb * g)) * g⁻¹ =
      g * u * g⁻¹ * zb by group, hg] at h1)
  obtain ⟨c, hc, hcw⟩ := d.exists_conj_eq_forty hwu hw hw1 hwu'
  have hcu : c * (u : J ⧸ Subgroup.center J) = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine ⟨g * c⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
  · calc g * c⁻¹ * zb = g * c⁻¹ * (c * (g⁻¹ * zb * g) * c⁻¹) := by rw [hcw]
      _ = zb * (g * c⁻¹) := by group
  · calc g * c⁻¹ * (u : J ⧸ Subgroup.center J) * (g * c⁻¹)⁻¹ =
        g * (c⁻¹ * (u * c)) * g⁻¹ := by group
      _ = g * (c⁻¹ * (c * u)) * g⁻¹ := by rw [hcu]
      _ = s := by rw [← hg]; group

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

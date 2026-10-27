module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAction
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsShape
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSetup
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSevenPerm
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HSFLit.L2K

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.AutL2Facts

variable {X : Type} [Group X] {L : Subgroup X}

@[expose] noncomputable def barX (L : Subgroup X) (g : X) : L ⧸ pPrimeCore 2 L :=
  open Classical in if h : g ∈ L then QuotientGroup.mk ⟨g, h⟩ else 1

theorem barX_of_mem {g : X} (hg : g ∈ L) : barX L g = QuotientGroup.mk ⟨g, hg⟩ := by
  simp [barX, hg]

theorem barX_mul {g h : X} (hg : g ∈ L) (hh : h ∈ L) : barX L (g * h) = barX L g * barX L h := by
  rw [barX_of_mem hg, barX_of_mem hh, barX_of_mem (mul_mem hg hh), ← QuotientGroup.mk_mul]
  rfl

theorem barX_inv {g : X} (hg : g ∈ L) : barX L g⁻¹ = (barX L g)⁻¹ := by
  rw [barX_of_mem hg, barX_of_mem (inv_mem hg), ← QuotientGroup.mk_inv]
  rfl

theorem barX_one : barX L (1 : X) = 1 := by
  rw [barX_of_mem (one_mem _), show (⟨1, _⟩ : L) = 1 from rfl, QuotientGroup.mk_one]

theorem barX_conj {g h : X} (hg : g ∈ L) (hh : h ∈ L) :
    barX L (g * h * g⁻¹) = barX L g * barX L h * (barX L g)⁻¹ := by
  rw [barX_mul (mul_mem hg hh) (inv_mem hg), barX_mul hg hh, barX_inv hg]

abbrev oddCoreL (L : Subgroup X) : Subgroup X := (pPrimeCore 2 L).map L.subtype

theorem oddCoreL_le : oddCoreL L ≤ L := map_subtype_le _

theorem barX_eq_one_iff {g : X} (hg : g ∈ L) : barX L g = 1 ↔ g ∈ oddCoreL L := by
  rw [barX_of_mem hg, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact hl

theorem conj_mem_oddCoreL {l o : X} (hl : l ∈ L) (ho : o ∈ oddCoreL L) :
    l * o * l⁻¹ ∈ oddCoreL L := by
  have hoL := oddCoreL_le ho
  rw [← barX_eq_one_iff (mul_mem (mul_mem hl hoL) (inv_mem hl)), barX_conj hl hoL,
    (barX_eq_one_iff hoL).mpr ho, mul_one, mul_inv_cancel]

theorem barX_conj_of_normalizer {κ g : X} (hκ : κ ∈ normalizer (L : Set X)) (hg : g ∈ L) :
    barX L (κ * g * κ⁻¹) = HarrisLit.barAction L ⟨κ, hκ⟩ (barX L g) := by
  rw [barX_of_mem hg, barX_of_mem ((mem_normalizer_iff.mp hκ g).mp hg), HarrisLit.barAction_mk]
  rfl

theorem conj_mem_oddCoreL_of_normalizer {κ o : X} (hκ : κ ∈ normalizer (L : Set X))
    (ho : o ∈ oddCoreL L) : κ * o * κ⁻¹ ∈ oddCoreL L := by
  have hoL := oddCoreL_le ho
  have hκo : κ * o * κ⁻¹ ∈ L := (mem_normalizer_iff.mp hκ o).mp hoL
  rw [← barX_eq_one_iff hκo, barX_conj_of_normalizer hκ hoL, (barX_eq_one_iff hoL).mpr ho,
    map_one]

variable [Finite X]

theorem odd_card_oddCoreL : Odd (Nat.card (oddCoreL L)) := by
  rw [card_map_of_injective L.subtype_injective]
  exact Config.odd_card_pPrimeCore

theorem inf_oddCoreL_eq_bot {P : Subgroup X} (hP : IsPGroup 2 P) {N : Subgroup X}
    (hN : N ≤ oddCoreL L) : N ⊓ P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  rw [hk]
  have hodd : Odd (Nat.card N) := Odd.of_dvd_nat odd_card_oddCoreL (Subgroup.card_dvd_of_le hN)
  exact Nat.Coprime.pow_right k hodd.coprime_two_right

theorem exists_fixed_of_barX {κ g₀ : X} (hκN : κ ∈ normalizer (L : Set X)) (hκ2 : κ ^ 2 = 1)
    (hg₀ : g₀ ∈ L) (hfix : barX L (κ * g₀ * κ⁻¹) = barX L g₀) :
    ∃ o ∈ oddCoreL L, κ * (g₀ * o) * κ⁻¹ = g₀ * o := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hκinv : κ⁻¹ = κ := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hκ2]
  have hκg₀ : κ * g₀ * κ⁻¹ ∈ L := (mem_normalizer_iff.mp hκN g₀).mp hg₀
  set m := g₀⁻¹ * (κ * g₀ * κ⁻¹) with hm
  have hmO : m ∈ oddCoreL L := by
    rw [← barX_eq_one_iff (mul_mem (inv_mem hg₀) hκg₀), barX_mul (inv_mem hg₀) hκg₀, hfix,
      barX_inv hg₀, inv_mul_cancel]
  have hσ : ∀ o ∈ oddCoreL L, m * (κ * o * κ⁻¹) ∈ oddCoreL L := fun o ho =>
    mul_mem hmO (conj_mem_oddCoreL_of_normalizer hκN ho)
  have hσσ : ∀ o : X, m * (κ * (m * (κ * o * κ⁻¹)) * κ⁻¹) = o := by
    intro o
    have hκκ : κ * κ = 1 := by rw [← pow_two, hκ2]
    have h1 : m * (κ * (m * (κ * o * κ⁻¹)) * κ⁻¹) =
        g₀⁻¹ * (κ * κ) * g₀ * o * (κ * κ)⁻¹ := by
      rw [hm]
      group
    rw [h1, hκκ]
    group
  let σ : Perm (oddCoreL L) :=
    { toFun := fun o => ⟨m * (κ * o * κ⁻¹), hσ o o.2⟩
      invFun := fun o => ⟨m * (κ * o * κ⁻¹), hσ o o.2⟩
      left_inv := fun o => Subtype.ext (hσσ o)
      right_inv := fun o => Subtype.ext (hσσ o) }
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    ext o
    change m * (κ * (m * (κ * o * κ⁻¹)) * κ⁻¹) = o
    exact hσσ o
  have : Fintype (oddCoreL L) := Fintype.ofFinite _
  have hnd : ¬ 2 ∣ Fintype.card (oddCoreL L) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.not_even_iff_odd.mpr odd_card_oddCoreL ∘ even_iff_two_dvd.mpr
  obtain ⟨o, ho⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hσ2
  have ho' : m * (κ * o * κ⁻¹) = o := congrArg Subtype.val ho
  refine ⟨o, o.2, ?_⟩
  calc κ * (g₀ * o) * κ⁻¹ = g₀ * (m * (κ * o * κ⁻¹)) := by rw [hm]; group
    _ = g₀ * o := by rw [ho']

theorem exists_lift {κ : X} (hκN : κ ∈ normalizer (L : Set X)) (hκ2 : κ ^ 2 = 1)
    {V : Subgroup X} (hVL : V ≤ L) (hV2 : IsPGroup 2 V) (hVκ : ∀ v ∈ V, κ * v = v * κ)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {g₀ : X} (hg₀ : g₀ ∈ L)
    (hfix : barX L (κ * g₀ * κ⁻¹) = barX L g₀)
    (hnorm : ∀ v ∈ V, ∃ v' ∈ V, barX L (g₀ * v * g₀⁻¹) = barX L v') :
    ∃ d ∈ L, d * κ = κ * d ∧ (∀ v ∈ V, d * v * d⁻¹ ∈ V) ∧
      ∀ v ∈ V, barX L (d * v * d⁻¹) = barX L (g₀ * v * g₀⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o, hoO, ho⟩ := exists_fixed_of_barX hκN hκ2 hg₀ hfix
  have hoL := oddCoreL_le hoO
  set g₁ := g₀ * o with hg₁
  have hg₁L : g₁ ∈ L := mul_mem hg₀ hoL
  have hg₁κ : g₁ * κ = κ * g₁ := by
    calc g₁ * κ = κ * g₁ * κ⁻¹ * κ := by rw [ho]
      _ = κ * g₁ := by group
  have hbarg₁ : barX L g₁ = barX L g₀ := by
    rw [hg₁, barX_mul hg₀ hoL, (barX_eq_one_iff hoL).mpr hoO, mul_one]
  set N : Subgroup X := oddCoreL L ⊓ centralizer ({κ} : Set X) with hN
  set W : Subgroup X := N ⊔ V with hW
  have hNV : V ≤ normalizer (N : Set X) := by
    intro v hv
    refine mem_normalizer_iff.mpr fun n => ⟨fun hn => ?_, fun hn => ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨conj_mem_oddCoreL (hVL hv) hn.1, ?_⟩
      have h1 := mem_centralizer_singleton_iff.mp hn.2
      have h2 := hVκ v hv
      rw [mem_centralizer_singleton_iff]
      calc v * n * v⁻¹ * κ = v * n * (v⁻¹ * κ) := by group
        _ = v * n * (κ * v⁻¹) := by
          rw [show v⁻¹ * κ = κ * v⁻¹ by
            calc v⁻¹ * κ = v⁻¹ * (κ * v) * v⁻¹ := by group
              _ = v⁻¹ * (v * κ) * v⁻¹ := by rw [h2]
              _ = κ * v⁻¹ := by group]
        _ = v * (n * κ) * v⁻¹ := by group
        _ = v * (κ * n) * v⁻¹ := by rw [h1]
        _ = κ * (v * n * v⁻¹) := by rw [← mul_assoc, ← mul_assoc, ← h2]; group
    · have hinv : v⁻¹ * (v * n * v⁻¹) * v⁻¹⁻¹ = n := by group
      have hmem : v⁻¹ * (v * n * v⁻¹) * v⁻¹⁻¹ ∈ N := by
        refine Subgroup.mem_inf.mpr ⟨by simpa using conj_mem_oddCoreL (inv_mem (hVL hv)) hn.1,
          ?_⟩
        have h1 := mem_centralizer_singleton_iff.mp hn.2
        have h2 := hVκ v hv
        rw [mem_centralizer_singleton_iff, inv_inv]
        calc v⁻¹ * (v * n * v⁻¹) * v * κ = v⁻¹ * (v * n * v⁻¹) * (v * κ) := by group
          _ = v⁻¹ * (v * n * v⁻¹) * (κ * v) := by rw [h2]
          _ = v⁻¹ * (v * n * v⁻¹ * κ) * v := by group
          _ = v⁻¹ * (κ * (v * n * v⁻¹)) * v := by rw [h1]
          _ = κ * (v⁻¹ * (v * n * v⁻¹) * v) := by
            have h3 : v⁻¹ * κ = κ * v⁻¹ := by
              calc v⁻¹ * κ = v⁻¹ * (κ * v) * v⁻¹ := by group
                _ = v⁻¹ * (v * κ) * v⁻¹ := by rw [h2]
                _ = κ * v⁻¹ := by group
            rw [← mul_assoc v⁻¹ κ, h3]
            group
      rwa [hinv] at hmem
  have hdisj : N ⊓ V = ⊥ := inf_oddCoreL_eq_bot hV2 inf_le_left
  have hcardW : Nat.card W = Nat.card N * Nat.card V :=
    card_sup_eq_mul_of_le_normalizer hNV hdisj
  have hNodd : Odd (Nat.card N) :=
    Odd.of_dvd_nat odd_card_oddCoreL (Subgroup.card_dvd_of_le inf_le_left)
  have hmax : ∀ Q : Subgroup X, Q ≤ W → IsPGroup 2 Q → Nat.card Q ≤ Nat.card V := by
    intro Q hQW hQ
    obtain ⟨a, ha⟩ := hQ.exists_card_eq
    have hdvd : Nat.card Q ∣ Nat.card N * Nat.card V := hcardW ▸ Subgroup.card_dvd_of_le hQW
    have hcop : Nat.Coprime (Nat.card Q) (Nat.card N) := by
      rw [ha]
      exact Nat.Coprime.pow_left a hNodd.coprime_two_left
    exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_left hdvd)
  have hVW : V ≤ W := le_sup_right
  have hWL : W ≤ L := sup_le (inf_le_left.trans oddCoreL_le) hVL
  have hWκ : W ≤ centralizer ({κ} : Set X) := by
    refine sup_le inf_le_right fun v hv => ?_
    rw [mem_centralizer_singleton_iff]
    exact (hVκ v hv).symm
  set V' : Subgroup X := V.map (MulAut.conj g₁).toMonoidHom with hV'
  have hV'W : V' ≤ W := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨v', hv', hbar⟩ := hnorm v hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hv'L := hVL hv'
    have hgvL : g₁ * v * g₁⁻¹ ∈ L := mul_mem (mul_mem hg₁L (hVL hv)) (inv_mem hg₁L)
    have hn : v'⁻¹ * (g₁ * v * g₁⁻¹) ∈ N := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← barX_eq_one_iff (mul_mem (inv_mem hv'L) hgvL), barX_mul (inv_mem hv'L) hgvL,
          barX_inv hv'L, barX_conj hg₁L (hVL hv), hbarg₁, ← barX_conj hg₀ (hVL hv), hbar,
          inv_mul_cancel]
      · rw [mem_centralizer_singleton_iff]
        have h1 := hVκ v hv
        have h2 := hVκ v' hv'
        have h3 : v'⁻¹ * κ = κ * v'⁻¹ := by
          calc v'⁻¹ * κ = v'⁻¹ * (κ * v') * v'⁻¹ := by group
            _ = v'⁻¹ * (v' * κ) * v'⁻¹ := by rw [h2]
            _ = κ * v'⁻¹ := by group
        have h4 : g₁⁻¹ * κ = κ * g₁⁻¹ := by
          calc g₁⁻¹ * κ = g₁⁻¹ * (κ * g₁) * g₁⁻¹ := by group
            _ = g₁⁻¹ * (g₁ * κ) * g₁⁻¹ := by rw [hg₁κ]
            _ = κ * g₁⁻¹ := by group
        calc v'⁻¹ * (g₁ * v * g₁⁻¹) * κ = v'⁻¹ * g₁ * v * (g₁⁻¹ * κ) := by group
          _ = v'⁻¹ * g₁ * (v * κ) * g₁⁻¹ := by rw [h4]; group
          _ = v'⁻¹ * (g₁ * κ) * v * g₁⁻¹ := by rw [← h1]; group
          _ = (v'⁻¹ * κ) * g₁ * v * g₁⁻¹ := by rw [hg₁κ]; group
          _ = κ * (v'⁻¹ * (g₁ * v * g₁⁻¹)) := by rw [h3]; group
    have : g₁ * v * g₁⁻¹ = v' * (v'⁻¹ * (g₁ * v * g₁⁻¹)) := by group
    rw [this]
    exact mul_mem (hVW hv') (le_sup_left (a := N) hn)
  have hsylV : IsSylowIn V W := by
    refine ⟨hVW, hV2, fun Q hQW hQ hVQ => ?_⟩
    exact (Subgroup.eq_of_le_of_card_ge hVQ (hmax Q hQW hQ)).symm
  have hV'2 : IsPGroup 2 V' := hV2.map _
  have hcardV' : Nat.card V' = Nat.card V := card_map_of_injective (MulAut.conj g₁).injective
  have hsylV' : IsSylowIn V' W := by
    refine ⟨hV'W, hV'2, fun Q hQW hQ hVQ => ?_⟩
    exact (Subgroup.eq_of_le_of_card_ge hVQ (hcardV' ▸ hmax Q hQW hQ)).symm
  obtain ⟨m, hmW, hmV⟩ := IsSylowIn.exists_conj hsylV' hsylV
  have hmL := hWL hmW
  have hmκ : m * κ = κ * m := (mem_centralizer_singleton_iff.mp (hWκ hmW))
  let S : Subgroup X :=
    { carrier := {w | w ∈ L ∧ ∃ v ∈ V, barX L w = barX L v}
      one_mem' := ⟨one_mem _, 1, one_mem _, rfl⟩
      mul_mem' := by
        rintro a b ⟨haL, va, hva, ha⟩ ⟨hbL, vb, hvb, hb⟩
        exact ⟨mul_mem haL hbL, va * vb, mul_mem hva hvb, by
          rw [barX_mul haL hbL, barX_mul (hVL hva) (hVL hvb), ha, hb]⟩
      inv_mem' := by
        rintro a ⟨haL, va, hva, ha⟩
        exact ⟨inv_mem haL, va⁻¹, inv_mem hva, by rw [barX_inv haL, barX_inv (hVL hva), ha]⟩ }
  have hWS : W ≤ S := by
    refine sup_le (fun n hn => ⟨oddCoreL_le hn.1, 1, one_mem _, ?_⟩)
      (fun v hv => ⟨hVL hv, v, hv, rfl⟩)
    rw [(barX_eq_one_iff (oddCoreL_le hn.1)).mpr hn.1, barX_one]
  obtain ⟨-, v₁, hv₁, hmv₁⟩ := hWS hmW
  refine ⟨m * g₁, mul_mem hmL hg₁L, ?_, fun v hv => ?_, fun v hv => ?_⟩
  · calc m * g₁ * κ = m * (g₁ * κ) := by group
      _ = m * κ * g₁ := by rw [hg₁κ]; group
      _ = κ * (m * g₁) := by rw [hmκ]; group
  · have : m * (g₁ * v * g₁⁻¹) * m⁻¹ ∈ V'.map (MulAut.conj m).toMonoidHom :=
      ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    rw [← hmV] at this
    simpa [mul_assoc] using this
  · obtain ⟨v', hv', hbar⟩ := hnorm v hv
    have hvL := hVL hv
    have e1 : m * g₁ * v * (m * g₁)⁻¹ = m * (g₁ * v * g₁⁻¹) * m⁻¹ := by group
    rw [e1, barX_conj hmL (mul_mem (mul_mem hg₁L hvL) (inv_mem hg₁L)), barX_conj hg₁L hvL,
      hbarg₁, ← barX_conj hg₀ hvL, hbar, hmv₁, ← barX_conj (hVL hv₁) (hVL hv'),
      show v₁ * v' * v₁⁻¹ = v' by rw [hVc v₁ hv₁ v' hv']; group]

end CFSG.ComponentClassification.HSFLit.L2K

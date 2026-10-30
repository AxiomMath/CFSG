module

public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Quot
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Generation
public import CFSG.LargeExtraspecial.AS35MAxB
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem exists_commutator_not_mem {R S L H : Subgroup G}
    (hSR : S ≤ R) (hS : IsPGroup 2 S)
    (hLR : L ≤ R) (hLn : R ≤ Subgroup.normalizer (L : Set G))
    (hH : H = S ⊓ L) (hHn : R ≤ Subgroup.normalizer (H : Set G))
    (hHmax : ∀ K : Subgroup G, K ≤ R → R ≤ Subgroup.normalizer (K : Set G) → IsPGroup 2 K →
      K ≤ H)
    (hRLS : (L : Set G) * (S : Set G) = (R : Set G))
    {z : G} (hzS : z ∈ S) (hzH : z ∉ H) :
    ∃ l ∈ L, z * l * z⁻¹ * l⁻¹ ∉ H := by
  by_contra hcon
  push Not at hcon
  have hHS : H ≤ S := hH ▸ inf_le_left
  have hHconj : ∀ r ∈ R, ∀ h ∈ H, r * h * r⁻¹ ∈ H := fun r hr h hh =>
    (Subgroup.mem_normalizer_iff.1 (hHn hr) h).1 hh
  have hLconj : ∀ r ∈ R, ∀ l ∈ L, r * l * r⁻¹ ∈ L := fun r hr l hl =>
    (Subgroup.mem_normalizer_iff.1 (hLn hr) l).1 hl
  let T : Subgroup G :=
    { carrier := {s | s ∈ S ∧ ∀ l ∈ L, s * l * s⁻¹ * l⁻¹ ∈ H}
      mul_mem' := by
        rintro s t ⟨hs, hs'⟩ ⟨ht, ht'⟩
        refine ⟨S.mul_mem hs ht, fun l hl => ?_⟩
        have h1 := hHconj s (hSR hs) _ (ht' l hl)
        have h2 := hs' l hl
        have := H.mul_mem h1 h2
        convert this using 1
        group
      one_mem' := ⟨S.one_mem, fun l _ => by simp⟩
      inv_mem' := by
        rintro s ⟨hs, hs'⟩
        refine ⟨S.inv_mem hs, fun l hl => ?_⟩
        have h1 := hHconj s⁻¹ (R.inv_mem (hSR hs)) _ (H.inv_mem (hs' l hl))
        convert h1 using 1
        group }
  have hTS : T ≤ S := fun s hs => hs.1
  have hconjS : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T := by
    intro s hs t ht
    refine ⟨S.mul_mem (S.mul_mem hs ht.1) (S.inv_mem hs), fun l hl => ?_⟩
    have hl'' : s⁻¹ * l * s⁻¹⁻¹ ∈ L := hLconj s⁻¹ (R.inv_mem (hSR hs)) l hl
    have h1 := hHconj s (hSR hs) _ (ht.2 _ hl'')
    convert h1 using 1
    group
  have hconjL : ∀ l ∈ L, ∀ t ∈ T, l * t * l⁻¹ ∈ T := by
    intro l hl t ht
    have hh : l * t * l⁻¹ * t⁻¹ ∈ H := by
      have := hHconj l (hLR hl) _ (ht.2 l⁻¹ (L.inv_mem hl))
      convert this using 1
      group
    have e : l * t * l⁻¹ = (l * t * l⁻¹ * t⁻¹) * t := by group
    refine ⟨?_, fun l' hl' => ?_⟩
    · rw [e]
      exact S.mul_mem (hHS hh) ht.1
    · have := H.mul_mem (H.mul_mem hh (ht.2 l' hl')) (hHconj l' (hLR hl') _ (H.inv_mem hh))
      rw [e]
      convert this using 1
      group
  have hconjR : ∀ g ∈ R, ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro g hg t ht
    have hg' : g ∈ (L : Set G) * (S : Set G) := hRLS ▸ hg
    obtain ⟨l, hl, s, hs, rfl⟩ := Set.mem_mul.1 hg'
    have := hconjL l hl _ (hconjS s hs t ht)
    convert this using 1
    group
  have hTR : T ≤ R := hTS.trans hSR
  have hTn : R ≤ Subgroup.normalizer (T : Set G) := fun g hg =>
    Sec7.mem_normalizer_of_conj_mem (hconjR g hg) (fun x hx => by
      simpa using hconjR g⁻¹ (R.inv_mem hg) x hx)
  have hTle : T ≤ H := hHmax T hTR hTn (hS.to_le hTS)
  exact hzH (hTle ⟨hzS, fun l hl => hcon l hl⟩)

private theorem exists_inverted {Q : Type} [Group Q] [Finite Q] {X Ā : Subgroup Q} {ζ x₀ : Q}
    (hĀ : IsElemAbelian 2 Ā) (hĀX : Ā ≤ Subgroup.normalizer (X : Set Q)) (hX : Odd (Nat.card X))
    (hζ : ζ ∈ Ā) (hζ2 : ζ * ζ = 1) (hx₀ : x₀ ∈ X) (hx₀ζ : ζ * x₀ ≠ x₀ * ζ) :
    ∃ E : Subgroup Q, E ≤ Ā ∧ Nat.card Ā ≤ 2 * Nat.card E ∧ ζ ∉ E ∧
      ∃ ū ∈ X, ū ∈ Subgroup.centralizer (E : Set Q) ∧ ū ≠ 1 ∧ ζ * ū * ζ⁻¹ = ū⁻¹ ∧
        Odd (orderOf ū) := by
  have hgen := le_iSup_centralizer_index_two hĀ hĀX hX
  obtain ⟨E, hEĀ, hEcard, x, hx, hxζ⟩ : ∃ E : Subgroup Q, E ≤ Ā ∧ Nat.card Ā ≤ 2 * Nat.card E ∧
      ∃ x ∈ X ⊓ Subgroup.centralizer (E : Set Q), ζ * x ≠ x * ζ := by
    by_contra hcon
    push Not at hcon
    have hle : (⨆ (E : Subgroup Q) (_ : E ≤ Ā) (_ : Nat.card Ā ≤ 2 * Nat.card E),
        X ⊓ Subgroup.centralizer (E : Set Q)) ≤ Subgroup.centralizer {ζ} := by
      refine iSup_le fun E => iSup_le fun hE => iSup_le fun hcard x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcon E hE hcard x hx).symm
    have := hle (hgen hx₀)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact hx₀ζ this.symm
  obtain ⟨hxX, hxE⟩ := Subgroup.mem_inf.1 hx
  have hζE : ζ ∉ E := fun h => hxζ (Subgroup.mem_centralizer_iff.1 hxE ζ h)
  have hζi : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ2
  have hζx : ζ * x * ζ⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hĀX hζ) x).1 hxX
  have hūX : x⁻¹ * (ζ * x * ζ⁻¹) ∈ X := X.mul_mem (X.inv_mem hxX) hζx
  refine ⟨E, hEĀ, hEcard, hζE, x⁻¹ * (ζ * x * ζ⁻¹), hūX, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 : Commute e x := Subgroup.mem_centralizer_iff.1 hxE e he
    have h2 : Commute e ζ := hĀ.comm (hEĀ he) hζ
    exact ((h1.inv_right).mul_right ((h2.mul_right h1).mul_right h2.inv_right)).eq
  · intro h1
    apply hxζ
    have h2 : ζ * x * ζ⁻¹ = x := (inv_mul_eq_one.1 h1).symm
    calc ζ * x = ζ * x * ζ⁻¹ * ζ := by group
      _ = x * ζ := by rw [h2]
  · rw [hζi]
    have e1 : ζ * (x⁻¹ * (ζ * x * ζ)) * ζ = ζ * x⁻¹ * ζ * x * (ζ * ζ) := by group
    rw [hζ2, mul_one] at e1
    rw [e1]
    simp only [mul_inv_rev, inv_inv, hζi, mul_assoc]
  · exact Odd.of_dvd_nat hX (Subgroup.orderOf_dvd_natCard X hūX)

private theorem exists_u_B {R S L H A : Subgroup G}
    (hSR : S ≤ R) (hLR : L ≤ R) (hLn : R ≤ Subgroup.normalizer (L : Set G))
    (hH : H = S ⊓ L) (hHn : R ≤ Subgroup.normalizer (H : Set G))
    (hLodd : ¬ 2 ∣ H.relIndex L)
    (hAS : A ≤ S) (hAe : IsElemAbelian 2 A)
    {z : G} (hzA : z ∈ A) (hz2 : z * z = 1)
    (hcomm : ∃ l ∈ L, z * l * z⁻¹ * l⁻¹ ∉ H) :
    ∃ u ∈ L, ∃ B : Subgroup G, B ≤ A ∧ Nat.card A ≤ 2 * Nat.card B ∧
      (∀ b ∈ B, u * b * u⁻¹ * b⁻¹ ∈ H) ∧ z ∉ H ⊔ B ∧
      ∀ k : ℕ, (z * (u⁻¹ * z * u)) ^ (2 ^ k) ∉ H := by
  have hHS : H ≤ S := hH ▸ inf_le_left
  have hHL : H ≤ L := hH ▸ inf_le_right
  have hHR : H ≤ R := hHS.trans hSR
  have hAR : A ≤ R := hAS.trans hSR
  have hzR : z ∈ R := hAR hzA
  haveI : (H.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHR).2 hHn
  obtain ⟨l, hlL, hl⟩ := hcomm
  have hlR : l ∈ R := hLR hlL
  let z' : ↥R := ⟨z, hzR⟩
  let l' : ↥R := ⟨l, hlR⟩
  let π := QuotientGroup.mk' (H.subgroupOf R)
  have hXodd : Odd (Nat.card (bar R H L)) := odd_card_bar hLR hHL hLodd
  have hĀe : IsElemAbelian 2 (bar R H A) := isElemAbelian_bar hAe
  have hĀX : bar R H A ≤ Subgroup.normalizer ((bar R H L : Subgroup _) : Set _) :=
    bar_le_normalizer hAR hLR (hAR.trans hLn)
  have hζĀ : π z' ∈ bar R H A := mk_mem_bar hzA
  have hζ2 : π z' * π z' = 1 := by
    rw [← map_mul]
    have : z' * z' = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hx₀ : π l' ∈ bar R H L := mk_mem_bar hlL
  have hx₀ζ : π z' * π l' ≠ π l' * π z' := fun h => hl ((mk_commute_iff z' l').1 h)
  obtain ⟨E, hEĀ, hEcard, hζE, ū, hūX, hūC, hū1, hūinv, hūodd⟩ :=
    exists_inverted hĀe hĀX hXodd hζĀ hζ2 hx₀ hx₀ζ
  obtain ⟨u', hu'L, hu'⟩ := Subgroup.mem_map.1 hūX
  have hu'L' : (u' : G) ∈ L := Subgroup.mem_subgroupOf.1 hu'L
  refine ⟨(u' : G), hu'L', barPre R H A E, barPre_le A E,
    card_le_two_mul_card_barPre hAR hEĀ hEcard, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨hbA, hbR, hbE⟩ := mem_barPre_iff.1 hb
    have h1 : π ⟨b, hbR⟩ * ū = ū * π ⟨b, hbR⟩ := Subgroup.mem_centralizer_iff.1 hūC _ hbE
    rw [← hu'] at h1
    exact (mk_commute_iff u' ⟨b, hbR⟩).1 h1.symm
  · intro hzmem
    let PE : Subgroup G := (E.comap π).map R.subtype
    have hHPE : H ≤ PE := by
      intro h hh
      refine Subgroup.mem_map.2 ⟨⟨h, hHR hh⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap, (mk_eq_one_iff ⟨h, hHR hh⟩).2 hh]
      exact E.one_mem
    have hBPE : barPre R H A E ≤ PE := inf_le_right
    obtain ⟨r, hr, hrz⟩ := Subgroup.mem_map.1 (sup_le hHPE hBPE hzmem)
    have : r = z' := Subtype.ext hrz
    exact hζE (this ▸ hr)
  · intro k hk
    have h1 : π ((z' * (u'⁻¹ * z' * u')) ^ (2 ^ k)) = 1 := by
      rw [mk_eq_one_iff]
      simpa [Subgroup.coe_pow] using hk
    have hζi : (π z')⁻¹ = π z' := inv_eq_of_mul_eq_one_right hζ2
    have hinv2 : π z' * ū⁻¹ * (π z')⁻¹ = ū := by
      have : π z' * ū⁻¹ * (π z')⁻¹ = (π z' * ū * (π z')⁻¹)⁻¹ := by group
      rw [this, hūinv, inv_inv]
    have h2 : π (z' * (u'⁻¹ * z' * u')) = ū * ū := by
      have e : π z' * (ū⁻¹ * π z' * ū) =
          (π z' * ū⁻¹ * (π z')⁻¹) * (π z' * π z') * ū := by group
      rw [map_mul, map_mul, map_mul, map_inv, hu', e, hinv2, hζ2, mul_one]
    rw [map_pow, h2, ← sq, ← pow_mul] at h1
    have h3 : orderOf ū ∣ 2 ^ (k + 1) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_succ, mul_comm]; exact h1)
    have h4 : Nat.Coprime (orderOf ū) (2 ^ (k + 1)) :=
      (Nat.coprime_two_right.mpr hūodd).pow_right _
    exact hū1 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 h3))

private theorem mem_normalizer_sup {H B : Subgroup G} {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgB : ∀ b ∈ B, g * b = b * g) :
    g ∈ Subgroup.normalizer ((H ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (H : Set G) → (∀ b ∈ B, g * b = b * g) →
      ∀ x ∈ H ⊔ B, g * x * g⁻¹ ∈ H ⊔ B := by
    intro g hgH hgB x hx
    have hle : (H ⊔ B).map (MulAut.conj g).toMonoidHom ≤ H ⊔ B := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨h, hh, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 hgH h).1 hh
      · rintro _ ⟨b, hb, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show g * b * g⁻¹ = b by rw [hgB b hb]; group]
        exact hb
    exact hle ⟨x, hx, rfl⟩
  exact Sec7.mem_normalizer_of_conj_mem (key hgH hgB) (fun x hx => by
    simpa using key (inv_mem hgH)
      (fun b hb => (Commute.inv_left (show Commute g b from hgB b hb)).eq) x hx)

private theorem conj_mem_P {H B : Subgroup G} {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgB : ∀ b ∈ B, g * b = b * g)
    {x : G} (hx : x ∈ (H ⊔ B) ⊓ Subgroup.centralizer (B : Set G)) :
    g * x * g⁻¹ ∈ (H ⊔ B) ⊓ Subgroup.centralizer (B : Set G) := by
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2
    ⟨(Subgroup.mem_normalizer_iff.1 (mem_normalizer_sup hgH hgB) x).1 hx1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h1 : Commute b g := (show Commute g b from hgB b hb).symm
  have h2 : Commute b x := Subgroup.mem_centralizer_iff.1 hx2 b hb
  exact ((h1.mul_right h2).mul_right h1.inv_right).eq

private theorem two_pow_pred_le_of_le_mul {m n : ℕ} (hn : 0 < n) (h : 2 ^ m ≤ 2 * n) :
    2 ^ (m - 1) ≤ n := by
  cases m with
  | zero => simp only [Nat.zero_sub, pow_zero]; exact hn
  | succ m =>
    rw [pow_succ] at h
    simpa using Nat.le_of_mul_le_mul_right (by linarith : 2 ^ m * 2 ≤ n * 2) (by norm_num : 0 < 2)

private theorem conj_centralizes {S H B A : Subgroup G} {z u : G}
    (hHS : H ≤ S) (hBA : B ≤ A) (hAS : A ≤ S) (hAe : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ pRank 2 S) (hcard : Nat.card A ≤ 2 * Nat.card B)
    (hz : z ∈ omegaOneZ (jOneOf S)) (hu : ∀ b ∈ B, u * b * u⁻¹ * b⁻¹ ∈ H) :
    ∀ b ∈ B, (u⁻¹ * z * u) * b = b * (u⁻¹ * z * u) := by
  intro b hb
  let E : Subgroup G := B.map (MulAut.conj u).toMonoidHom
  have hES : E ≤ S := by
    rintro _ ⟨b', hb', rfl⟩
    have e : (MulAut.conj u).toMonoidHom b' = (u * b' * u⁻¹ * b'⁻¹) * b' := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact S.mul_mem (hHS (hu b' hb')) (hAS (hBA hb'))
  have hEe : IsElemAbelian 2 E := (hAe.mono hBA).map _
  have hEcard : 2 ^ (pRank 2 S - 1) ≤ Nat.card E := by
    rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]
    exact two_pow_pred_le_of_le_mul Nat.card_pos (hAcard ▸ hcard)
  have hEJ : E ≤ jOneOf S := le_jOneOf hES hEe hEcard
  have hzc := omegaOneZ_le_centralizer (jOneOf S) hz
  have hub : u * b * u⁻¹ ∈ jOneOf S := hEJ ⟨b, hb, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1 hzc _ hub
  calc (u⁻¹ * z * u) * b = u⁻¹ * (z * (u * b * u⁻¹)) * u := by group
    _ = u⁻¹ * ((u * b * u⁻¹) * z) * u := by rw [h1]
    _ = b * (u⁻¹ * z * u) := by group

private theorem exists_w {R B H : Subgroup G} {z v : G}
    (hz2 : z * z = 1) (hv2 : v * v = 1) (hzR : z ∈ R) (hvR : v ∈ R)
    (hzB : ∀ b ∈ B, z * b = b * z) (hvB : ∀ b ∈ B, v * b = b * v)
    (hpow : ∀ k : ℕ, (z * v) ^ (2 ^ k) ∉ H) :
    ∃ w : G, w ∈ R ∧ (∀ b ∈ B, w * b = b * w) ∧ Odd (orderOf w) ∧ z * w * z⁻¹ = w⁻¹ ∧
      w ∉ H := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hzd : z * (z * v) * z⁻¹ = (z * v)⁻¹ := by
    rw [mul_inv_rev, hzi, hvi]
    calc z * (z * v) * z = (z * z) * v * z := by group
      _ = v * z := by rw [hz2, one_mul]
  obtain ⟨a, b, hb, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (z * v)).ne'
  refine ⟨(z * v) ^ (2 ^ a), R.pow_mem (R.mul_mem hzR hvR) _, fun c hc => ?_, ?_, ?_, hpow a⟩
  · exact (Commute.pow_left ((show Commute z c from hzB c hc).mul_left
      (show Commute v c from hvB c hc)) _).eq
  · rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨b, hm⟩, hm,
      Nat.mul_div_cancel_left b (pow_pos two_pos a)]
    exact hb
  · have h := map_pow (MulAut.conj z) (z * v) (2 ^ a)
    simp only [MulAut.conj_apply] at h
    rw [h, hzd, inv_pow]

private theorem exists_not_comm {R S H B A : Subgroup G} {w : G}
    (hS : IsPGroup 2 S) (hHS : H ≤ S) (hBA : B ≤ A) (hAS : A ≤ S)
    (hHn : R ≤ Subgroup.normalizer (H : Set G))
    (hHc : ∀ x ∈ R, (∀ h ∈ H, h * x = x * h) → x ∈ H)
    (hwR : w ∈ R) (hwodd : Odd (orderOf w)) (hwB : ∀ b ∈ B, w * b = b * w) (hwH : w ∉ H) :
    ∃ q ∈ (H ⊔ B) ⊓ Subgroup.centralizer (B : Set G), w * q ≠ q * w := by
  by_contra hcon
  push Not at hcon
  have hQS : H ⊔ B ≤ S := sup_le hHS (hBA.trans hAS)
  have hfix : ∀ q ∈ H ⊔ B, (∀ b ∈ B, q * b = b * q) → w * q = q * w := fun q hq hqB =>
    hcon q (Subgroup.mem_inf.2 ⟨hq, Subgroup.mem_centralizer_iff.2 fun b hb => (hqB b hb).symm⟩)
  have key := CFSG.LargeExtraspecial.AS35M.commute_of_thompson_AxB (hS.to_le hQS)
    (hS.to_le (hBA.trans hAS)) (mem_normalizer_sup (hHn hwR) hwB)
    (le_sup_right.trans Subgroup.le_normalizer) hwodd hwB hfix
  exact hwH (hHc w hwR fun h hh => (key h (Subgroup.mem_sup_left hh)).symm)

private theorem comm_of_stab {P B : Subgroup G} {z w : G}
    (hB2 : ∀ b ∈ B, b * b = 1)
    (hzB : ∀ b ∈ B, z * b = b * z) (hwB : ∀ b ∈ B, w * b = b * w)
    (hz2 : z * z = 1) (hzw : z * w * z⁻¹ = w⁻¹) (hw : Odd (orderOf w))
    (hwP : ∀ x ∈ P, w * x * w⁻¹ ∈ P)
    (hz : ∀ x ∈ P, x⁻¹ * (z * x * z⁻¹) ∈ B) :
    ∀ x ∈ P, w * x = x * w := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hwB' : ∀ b ∈ B, w * b * w⁻¹ = b := fun b hb => by rw [hwB b hb]; group
  have hzB' : ∀ b ∈ B, z * b * z⁻¹ = b := fun b hb => by rw [hzB b hb]; group
  have hzw' : z * w⁻¹ * z⁻¹ = w := by
    calc z * w⁻¹ * z⁻¹ = (z * w * z⁻¹)⁻¹ := by group
      _ = w := by rw [hzw, inv_inv]
  have c1 : ∀ x ∈ P, ∃ b ∈ B, w⁻¹ * x * w = (w * x * w⁻¹) * b := by
    intro x hx
    obtain ⟨b₁, hb₁, hxb₁⟩ : ∃ b ∈ B, z⁻¹ * x * z = x * b :=
      ⟨_, hz x hx, by rw [hzi]; group⟩
    obtain ⟨b₂, hb₂, hxb₂⟩ : ∃ b ∈ B, z * (w * x * w⁻¹) * z⁻¹ = (w * x * w⁻¹) * b :=
      ⟨_, hz _ (hwP x hx), by group⟩
    refine ⟨b₂ * b₁, B.mul_mem hb₂ hb₁, ?_⟩
    calc w⁻¹ * x * w = (z * w * z⁻¹) * x * (z * w⁻¹ * z⁻¹) := by rw [hzw, hzw']
      _ = z * (w * (z⁻¹ * x * z) * w⁻¹) * z⁻¹ := by group
      _ = z * (w * (x * b₁) * w⁻¹) * z⁻¹ := by rw [hxb₁]
      _ = z * ((w * x * w⁻¹) * (w * b₁ * w⁻¹)) * z⁻¹ := by group
      _ = z * ((w * x * w⁻¹) * b₁) * z⁻¹ := by rw [hwB' b₁ hb₁]
      _ = (z * (w * x * w⁻¹) * z⁻¹) * (z * b₁ * z⁻¹) := by group
      _ = ((w * x * w⁻¹) * b₂) * b₁ := by rw [hxb₂, hzB' b₁ hb₁]
      _ = (w * x * w⁻¹) * (b₂ * b₁) := by group
  have c2 : ∀ x ∈ P, ∃ b ∈ B, w ^ 2 * x * (w ^ 2)⁻¹ = x * b := by
    intro x hx
    obtain ⟨b, hb, h⟩ := c1 (w * x * w⁻¹) (hwP x hx)
    refine ⟨b⁻¹, B.inv_mem hb, ?_⟩
    have e1 : x = (w ^ 2 * x * (w ^ 2)⁻¹) * b := by
      calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
        _ = (w * (w * x * w⁻¹) * w⁻¹) * b := h
        _ = (w ^ 2 * x * (w ^ 2)⁻¹) * b := by rw [pow_two]; group
    calc w ^ 2 * x * (w ^ 2)⁻¹ = ((w ^ 2 * x * (w ^ 2)⁻¹) * b) * b⁻¹ := by group
      _ = x * b⁻¹ := by rw [← e1]
  have hw2B : ∀ b ∈ B, w ^ 2 * b * (w ^ 2)⁻¹ = b := by
    intro b hb
    calc w ^ 2 * b * (w ^ 2)⁻¹ = w * (w * b * w⁻¹) * w⁻¹ := by rw [pow_two]; group
      _ = b := by rw [hwB' b hb, hwB' b hb]
  have c3 : ∀ i : ℕ, ∀ x ∈ P, ∃ b ∈ B, (w ^ 2) ^ i * x * ((w ^ 2) ^ i)⁻¹ = x * b := by
    intro i
    induction i with
    | zero => intro x hx; exact ⟨1, B.one_mem, by simp⟩
    | succ i ih =>
      intro x hx
      obtain ⟨b, hb, h1⟩ := ih x hx
      obtain ⟨b', hb', h2⟩ := c2 x hx
      refine ⟨b' * b, B.mul_mem hb' hb, ?_⟩
      calc (w ^ 2) ^ (i + 1) * x * ((w ^ 2) ^ (i + 1))⁻¹
          = w ^ 2 * ((w ^ 2) ^ i * x * ((w ^ 2) ^ i)⁻¹) * (w ^ 2)⁻¹ := by group
        _ = w ^ 2 * (x * b) * (w ^ 2)⁻¹ := by rw [h1]
        _ = (w ^ 2 * x * (w ^ 2)⁻¹) * (w ^ 2 * b * (w ^ 2)⁻¹) := by group
        _ = (x * b') * b := by rw [h2, hw2B b hb]
        _ = x * (b' * b) := by group
  obtain ⟨i, hi⟩ := hw
  have hwi : w ^ (orderOf w) = 1 := pow_orderOf_eq_one w
  have hw2i : (w ^ 2) ^ i = w⁻¹ := by
    rw [← pow_mul]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    rw [hi] at hwi
    exact hwi
  have c4 : ∀ x ∈ P, ∃ b ∈ B, w⁻¹ * x * w = x * b := by
    intro x hx
    obtain ⟨b, hb, h⟩ := c3 i x hx
    rw [hw2i] at h
    exact ⟨b, hb, by simpa using h⟩
  have c5 : ∀ x ∈ P, ∃ β ∈ B, w * x * w⁻¹ = x * β := by
    intro x hx
    obtain ⟨b, hb, h⟩ := c4 (w * x * w⁻¹) (hwP x hx)
    refine ⟨b⁻¹, B.inv_mem hb, ?_⟩
    have e1 : x = (w * x * w⁻¹) * b := by
      calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
        _ = (w * x * w⁻¹) * b := h
    calc w * x * w⁻¹ = ((w * x * w⁻¹) * b) * b⁻¹ := by group
      _ = x * b⁻¹ := by rw [← e1]
  intro x hx
  obtain ⟨β, hβ, hxβ⟩ := c5 x hx
  have c6 : ∀ n : ℕ, w ^ n * x * (w ^ n)⁻¹ = x * β ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc w ^ (n + 1) * x * (w ^ (n + 1))⁻¹ = w * (w ^ n * x * (w ^ n)⁻¹) * w⁻¹ := by group
        _ = w * (x * β ^ n) * w⁻¹ := by rw [ih]
        _ = (w * x * w⁻¹) * (w * β ^ n * w⁻¹) := by group
        _ = (x * β) * β ^ n := by rw [hxβ, hwB' _ (B.pow_mem hβ n)]
        _ = x * β ^ (n + 1) := by group
  have h1 := c6 (orderOf w)
  rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at h1
  have h2 : β ^ orderOf w = 1 :=
    mul_left_cancel (a := x) (by rw [mul_one]; exact h1.symm)
  have h3 : β ^ orderOf w = β := by
    rw [hi, pow_succ, pow_mul, sq, hB2 β hβ, one_pow, one_mul]
  have h4 : β = 1 := h3.symm.trans h2
  rw [h4, mul_one] at hxβ
  calc w * x = (w * x * w⁻¹) * w := by group
    _ = x * w := by rw [hxβ]

private theorem false_of_y {S H B A : Subgroup G} {z y : G}
    (hHS : H ≤ S) (hBA : B ≤ A) (hAS : A ≤ S) (hAe : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ pRank 2 S) (hcard : Nat.card A ≤ 2 * Nat.card B)
    (hzS : z ∈ S) (hz2 : z * z = 1) (hzB : ∀ b ∈ B, z * b = b * z)
    (hz : z ∈ omegaOneZ (jOneOf S)) (hznot : z ∉ H ⊔ B)
    (hyQ : y ∈ H ⊔ B) (hyB : ∀ b ∈ B, y * b = b * y) (hyinv : z * y * z⁻¹ = y⁻¹)
    (hyn : y ∉ B) : False := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hQS : H ⊔ B ≤ S := sup_le hHS (hBA.trans hAS)
  have hzy2 : (z * y) * (z * y) = 1 := by
    calc (z * y) * (z * y) = (z * y * z⁻¹) * y := by rw [hzi]; group
      _ = 1 := by rw [hyinv]; group
  have hzyQ : z * y ∉ H ⊔ B := fun h => hznot (by
    have := (H ⊔ B).mul_mem h ((H ⊔ B).inv_mem hyQ)
    simpa using this)
  have hzyB : ∀ b ∈ B, (z * y) * b = b * (z * y) := fun b hb => by
    rw [mul_assoc, hyB b hb, ← mul_assoc, hzB b hb, mul_assoc]
  have hcomm : ∀ a ∈ Subgroup.zpowers (z * y), ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute (z * y) b from hzyB b hb) k).eq
  have hFe : IsElemAbelian 2 (Subgroup.zpowers (z * y) ⊔ B) :=
    IsElemAbelian.sup_of_commute (isElemAbelian_zpowers (by rw [pow_two]; exact hzy2))
      (hAe.mono hBA) hcomm
  have hFS : Subgroup.zpowers (z * y) ⊔ B ≤ S :=
    sup_le (Subgroup.zpowers_le.2 (S.mul_mem hzS (hQS hyQ))) (hBA.trans hAS)
  have hzyF : z * y ∈ Subgroup.zpowers (z * y) ⊔ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hBF : B ≤ Subgroup.zpowers (z * y) ⊔ B := le_sup_right
  have hlt : Nat.card B < Nat.card (Subgroup.zpowers (z * y) ⊔ B : Subgroup G) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hBF) fun h => ?_
    have hBF' : B = Subgroup.zpowers (z * y) ⊔ B := Subgroup.eq_of_le_of_card_ge hBF h.ge
    exact hzyQ (Subgroup.mem_sup_right (hBF' ▸ hzyF))
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hBF
  have hc1 : 1 < c := Nat.lt_of_mul_lt_mul_left (a := Nat.card B) (by rw [mul_one, ← hc]; exact hlt)
  have h2B : 2 * Nat.card B ≤ Nat.card (Subgroup.zpowers (z * y) ⊔ B : Subgroup G) := by
    rw [hc, mul_comm]
    exact Nat.mul_le_mul_left _ hc1
  obtain ⟨k, hk⟩ := hFe.isPGroup.exists_card_eq
  have hkS : k ≤ CFSG.Open.pRank 2 S := CFSG.SectionRank.le_pRank Nat.one_lt_two hFS hFe hk
  have hFle : Nat.card (Subgroup.zpowers (z * y) ⊔ B : Subgroup G) ≤ 2 ^ pRank 2 S := by
    rw [hk, CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact Nat.pow_le_pow_right (by norm_num) hkS
  have hFge : 2 ^ pRank 2 S ≤ Nat.card (Subgroup.zpowers (z * y) ⊔ B : Subgroup G) := by
    rw [← hAcard]
    exact hcard.trans h2B
  have hzF : z ∈ Subgroup.zpowers (z * y) ⊔ B :=
    omegaOneZ_jOneOf_le hFS hFe (le_antisymm hFle hFge) hz
  obtain ⟨-, hFset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers (z * y)) B hcomm
  have hzF' : z ∈ ((Subgroup.zpowers (z * y) : Set G) * (B : Set G)) := by
    rw [← hFset]; exact hzF
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hzF'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have h1 : (z * y) ^ (2 * m) = 1 := by rw [zpow_mul, zpow_two, hzy2, one_zpow]
    rw [h1, one_mul] at hab
    exact hznot (hab ▸ Subgroup.mem_sup_right hb)
  · have h1 : (z * y) ^ (2 * m + 1) = z * y := by
      rw [zpow_add_one, zpow_mul, zpow_two, hzy2, one_zpow, one_mul]
    rw [h1] at hab
    have h2 : z * (y * b) = z * 1 := by rw [mul_one, ← mul_assoc]; exact hab
    have h3 : y = b⁻¹ := eq_inv_of_mul_eq_one_left (mul_left_cancel h2)
    exact hyn (h3 ▸ B.inv_mem hb)

private theorem false_of_u_B {R S H A B : Subgroup G} {z u : G}
    (hSR : S ≤ R) (hS : IsPGroup 2 S) (hHS : H ≤ S)
    (hHn : R ≤ Subgroup.normalizer (H : Set G))
    (hHc : ∀ x ∈ R, (∀ h ∈ H, h * x = x * h) → x ∈ H)
    (hAS : A ≤ S) (hAe : IsElemAbelian 2 A) (hAcard : Nat.card A = 2 ^ pRank 2 S)
    (hzA : z ∈ A) (hz : z ∈ omegaOneZ (jOneOf S)) (hz2 : z * z = 1) (huR : u ∈ R)
    (hBA : B ≤ A) (hBcard : Nat.card A ≤ 2 * Nat.card B)
    (hBcomm : ∀ b ∈ B, u * b * u⁻¹ * b⁻¹ ∈ H) (hzB : z ∉ H ⊔ B)
    (hpow : ∀ k : ℕ, (z * (u⁻¹ * z * u)) ^ (2 ^ k) ∉ H) : False := by
  have hzS : z ∈ S := hAS hzA
  have hzR : z ∈ R := hSR hzS
  have hzBc : ∀ b ∈ B, z * b = b * z := fun b hb => hAe.comm hzA (hBA hb)
  have hvB := conj_centralizes hHS hBA hAS hAe hAcard hBcard hz hBcomm
  have hv2 : (u⁻¹ * z * u) * (u⁻¹ * z * u) = 1 := by
    calc (u⁻¹ * z * u) * (u⁻¹ * z * u) = u⁻¹ * (z * z) * u := by group
      _ = 1 := by rw [hz2]; group
  have hvR : u⁻¹ * z * u ∈ R := R.mul_mem (R.mul_mem (R.inv_mem huR) hzR) huR
  obtain ⟨w, hwR, hwB, hwodd, hzw, hwH⟩ := exists_w hz2 hv2 hzR hvR hzBc hvB hpow
  obtain ⟨q, hqP, hwq⟩ := exists_not_comm hS hHS hBA hAS hHn hHc hwR hwodd hwB hwH
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => (hAe.mono hBA).mul_self_eq_one hb
  have hwP : ∀ x ∈ (H ⊔ B) ⊓ Subgroup.centralizer (B : Set G),
      w * x * w⁻¹ ∈ (H ⊔ B) ⊓ Subgroup.centralizer (B : Set G) :=
    fun x hx => conj_mem_P (hHn hwR) hwB hx
  have hzP : ∀ x ∈ (H ⊔ B) ⊓ Subgroup.centralizer (B : Set G),
      z * x * z⁻¹ ∈ (H ⊔ B) ⊓ Subgroup.centralizer (B : Set G) :=
    fun x hx => conj_mem_P (hHn hzR) hzBc hx
  obtain ⟨x, hxP, hxB⟩ : ∃ x ∈ (H ⊔ B) ⊓ Subgroup.centralizer (B : Set G),
      x⁻¹ * (z * x * z⁻¹) ∉ B := by
    by_contra hcon
    push Not at hcon
    exact hwq (comm_of_stab hB2 hzBc hwB hz2 hzw hwodd hwP hcon q hqP)
  have hyP : x⁻¹ * (z * x * z⁻¹) ∈ (H ⊔ B) ⊓ Subgroup.centralizer (B : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxP) (hzP x hxP)
  refine false_of_y hHS hBA hAS hAe hAcard hBcard hzS hz2 hzBc hz hzB (Subgroup.mem_inf.1 hyP).1
    (fun b hb => (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hyP).2 b hb).symm) ?_ hxB
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  rw [hzi]
  have e1 : z * (x⁻¹ * (z * x * z)) * z = z * x⁻¹ * z * x * (z * z) := by group
  rw [hz2, mul_one] at e1
  rw [e1]
  simp only [mul_inv_rev, inv_inv, hzi, mul_assoc]

theorem omegaOneZ_jOneOf_le_of_local {R S L H : Subgroup G}
    (hRs : Group.IsSolvable ↥R) (hSR : S ≤ R) (hS : IsPGroup 2 S)
    (hLR : L ≤ R) (hLn : R ≤ Subgroup.normalizer (L : Set G))
    (hH : H = S ⊓ L) (hHn : R ≤ Subgroup.normalizer (H : Set G))
    (hHmax : ∀ K : Subgroup G, K ≤ R → R ≤ Subgroup.normalizer (K : Set G) → IsPGroup 2 K →
      K ≤ H)
    (hHc : ∀ x ∈ R, (∀ h ∈ H, h * x = x * h) → x ∈ H)
    (hLodd : ¬ 2 ∣ H.relIndex L) (hRLS : (L : Set G) * (S : Set G) = (R : Set G)) :
    omegaOneZ (jOneOf S) ≤ H := by
  intro z hz
  by_contra hzH
  have hHS : H ≤ S := hH ▸ inf_le_left
  have hzS : z ∈ S := (Sec7.omegaOneZ_jOneOf_le S) hz
  have hz2 : z * z = 1 := (isElemAbelian_omegaOneZ (jOneOf S)).mul_self_eq_one hz
  obtain ⟨A, hAS, hAe, hAcard⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two S
  have hAcard' : Nat.card A = 2 ^ pRank 2 S := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hAcard
  have hzA : z ∈ A := omegaOneZ_jOneOf_le hAS hAe hAcard' hz
  obtain ⟨l, hlL, hl⟩ := exists_commutator_not_mem hSR hS hLR hLn hH hHn hHmax hRLS hzS hzH
  obtain ⟨u, huL, B, hBA, hBcard, hBcomm, hzB, hpow⟩ :=
    exists_u_B hSR hLR hLn hH hHn hLodd hAS hAe hzA hz2 ⟨l, hlL, hl⟩
  exact false_of_u_B hSR hS hHS hHn hHc hAS hAe hAcard' hzA hz hz2 (hLR huL) hBA hBcard hBcomm
    hzB hpow

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

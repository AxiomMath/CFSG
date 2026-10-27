module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Irr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Hexa

variable {G : Type} [Group G] [Finite G]

theorem conj_sq_eq_of_fpf {V : Subgroup G} (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hV2 : ∀ v ∈ V, v * v = 1) (hV16 : Nat.card V = 16) {t k : G}
    (htV : t ∈ normalizer (V : Set G)) (hkV : k ∈ normalizer (V : Set G))
    (ht3 : ∀ v ∈ V, t ^ 3 ^ 1 * v * (t ^ 3 ^ 1)⁻¹ = v)
    (htfix : ∀ v ∈ V, t * v * t⁻¹ = v → v = 1)
    (htk : ∀ v ∈ V, t * (k * v * k⁻¹) * t⁻¹ = k * (t * v * t⁻¹) * k⁻¹) {j : ℕ}
    (hkj : k ^ 2 ^ j = 1) {v : G} (hv : v ∈ V) : k * (k * v * k⁻¹) * k⁻¹ = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk2 : ∀ b ∈ V, k ^ 2 ^ j * b * (k ^ 2 ^ j)⁻¹ = b := fun b _ => by rw [hkj]; group
  have h3 : ∀ W : Subgroup G, W ≤ V → t ∈ normalizer (W : Set G) → Nat.card W ≡ 1 [MOD 3] :=
    fun W hWV htW => card_modEq_one_of_fix htW (fun b hb => ht3 b (hWV hb))
      (fun b hb h => htfix b (hWV hb) h)
  have hkb : ∀ b, b ∈ centralizer ({k} : Set G) → k * b * k⁻¹ = b := fun b hb => by
    rw [← mem_centralizer_singleton_iff.mp hb]
    group
  have htC : ∀ W : Subgroup G, W ≤ V → t ∈ normalizer (W : Set G) →
      t ∈ normalizer ((W ⊓ centralizer ({k} : Set G) : Subgroup G) : Set G) := by
    intro W hWV htW
    refine Sec2.mem_normalizer_of_forall_conj_mem fun b hb =>
      Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp htW b).mp hb.1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := htk b (hWV hb.1)
    rw [hkb b hb.2] at h1
    calc t * b * t⁻¹ * k = k * (t * b * t⁻¹) * k⁻¹ * k := by rw [← h1]
      _ = k * (t * b * t⁻¹) := by group
  set L := V ⊓ centralizer ({k} : Set G) with hL
  have hL3 : Nat.card L ≡ 1 [MOD 3] := h3 L inf_le_left (htC V le_rfl htV)
  have hL2 : Nat.card V ≡ Nat.card L [MOD 2] := card_modEq_card_inf_centralizer hkV hk2
  have hLdvd : Nat.card L ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hV16]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hiL⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hLdvd
  rw [hV16] at hL2
  have hvk : ∀ d ∈ V, d ∈ centralizer ({k} : Set G) → k * (v * d) * k⁻¹ = k * v * k⁻¹ * d :=
    fun d _ hd => by
      calc k * (v * d) * k⁻¹ = k * v * k⁻¹ * (k * d * k⁻¹) := by group
        _ = k * v * k⁻¹ * d := by rw [hkb d hd]
  interval_cases i
  · rw [hiL] at hL2; exact absurd hL2 (by decide)
  · rw [hiL] at hL3; exact absurd hL3 (by decide)
  ·
    let c : ↥V →* ↥V :=
      { toFun := fun w => ⟨k * w * k⁻¹, (mem_normalizer_iff.mp hkV w).mp w.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    let δ : ↥V →* ↥V :=
      { toFun := fun w => w⁻¹ * c w
        map_one' := by simp
        map_mul' := fun a b => Subtype.ext (by
          have h := hVab ((b : G)⁻¹) (inv_mem b.2) ((a : G)⁻¹ * (k * a * k⁻¹))
            (mul_mem (inv_mem a.2) (c a).2)
          show ((a : G) * b)⁻¹ * (k * (a * b) * k⁻¹) =
            (a : G)⁻¹ * (k * a * k⁻¹) * ((b : G)⁻¹ * (k * b * k⁻¹))
          calc ((a : G) * b)⁻¹ * (k * (a * b) * k⁻¹)
              = (b : G)⁻¹ * ((a : G)⁻¹ * (k * a * k⁻¹)) * (k * b * k⁻¹) := by group
            _ = (a : G)⁻¹ * (k * a * k⁻¹) * (b : G)⁻¹ * (k * b * k⁻¹) := by rw [h]
            _ = (a : G)⁻¹ * (k * a * k⁻¹) * ((b : G)⁻¹ * (k * b * k⁻¹)) := by group) }
    have hδ : ∀ w : ↥V, ((δ w : ↥V) : G) = (w : G)⁻¹ * (k * w * k⁻¹) := fun w => rfl
    have hker : δ.ker = L.subgroupOf V := by
      ext w
      rw [MonoidHom.mem_ker, mem_subgroupOf, Subtype.ext_iff, hδ]
      simp only [OneMemClass.coe_one, inv_mul_eq_one]
      constructor
      · intro h
        refine ⟨w.2, mem_centralizer_singleton_iff.mpr ?_⟩
        calc (w : G) * k = k * w * k⁻¹ * k := by rw [← h]
          _ = k * w := by group
      · intro h
        exact (hkb w h.2).symm
    have hcardM : Nat.card δ.range = 4 := by
      have h1 := Subgroup.card_ker_mul_card_range δ
      rw [hker, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : L ≤ V)).toEquiv, hiL,
        hV16] at h1
      omega
    set M := δ.range.map V.subtype with hM
    have hM4 : Nat.card M = 4 := by
      rw [hM, card_map_of_injective V.subtype_injective, hcardM]
    have hMV : M ≤ V := map_subtype_le _
    have hmemM : ∀ m ∈ M, ∃ w : ↥V, m = (w : G)⁻¹ * (k * w * k⁻¹) := by
      rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, rfl⟩
    have hδM : ∀ w : ↥V, (w : G)⁻¹ * (k * w * k⁻¹) ∈ M := fun w => ⟨δ w, ⟨w, rfl⟩, rfl⟩
    have htM : t ∈ normalizer (M : Set G) := Sec2.mem_normalizer_of_forall_conj_mem fun m hm => by
      obtain ⟨w, rfl⟩ := hmemM m hm
      have hw : t * w * t⁻¹ ∈ V := (mem_normalizer_iff.mp htV w).mp w.2
      have h1 := htk w w.2
      have e1 : t * ((w : G)⁻¹ * (k * w * k⁻¹)) * t⁻¹ =
          (t * w * t⁻¹)⁻¹ * (k * (t * w * t⁻¹) * k⁻¹) := by
        rw [← h1]
        group
      rw [e1]
      exact hδM ⟨_, hw⟩
    have hkM : k ∈ normalizer (M : Set G) := Sec2.mem_normalizer_of_forall_conj_mem fun m hm => by
      obtain ⟨w, rfl⟩ := hmemM m hm
      have hw : k * w * k⁻¹ ∈ V := (mem_normalizer_iff.mp hkV w).mp w.2
      have e1 : k * ((w : G)⁻¹ * (k * w * k⁻¹)) * k⁻¹ =
          (k * w * k⁻¹)⁻¹ * (k * (k * w * k⁻¹) * k⁻¹) := by group
      rw [e1]
      exact hδM ⟨_, hw⟩
    have hM2 : Nat.card M ≡ Nat.card (M ⊓ centralizer ({k} : Set G) : Subgroup G) [MOD 2] :=
      card_modEq_card_inf_centralizer hkM (fun b hb => hk2 b (hMV hb))
    have hM3 : Nat.card (M ⊓ centralizer ({k} : Set G) : Subgroup G) ≡ 1 [MOD 3] :=
      h3 _ (inf_le_left.trans hMV) (htC M hMV htM)
    have hMdvd : Nat.card (M ⊓ centralizer ({k} : Set G) : Subgroup G) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hM4]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i', hi', hiM⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hMdvd
    rw [hM4] at hM2
    have hMle : M ≤ centralizer ({k} : Set G) := by
      interval_cases i'
      · rw [hiM] at hM2; exact absurd hM2 (by decide)
      · rw [hiM] at hM3; exact absurd hM3 (by decide)
      · have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left :
          M ⊓ centralizer ({k} : Set G) ≤ M) (by rw [hM4, hiM]; norm_num)
        rw [← heq]
        exact inf_le_right
    have hd := hMle (hδM ⟨v, hv⟩)
    set d := v⁻¹ * (k * v * k⁻¹) with hd'
    have hdV : d ∈ V := hMV (hδM ⟨v, hv⟩)
    have e1 : k * v * k⁻¹ = v * d := by rw [hd']; group
    rw [e1, hvk d hdV hd, e1, mul_assoc, hV2 d hdV, mul_one]
  · rw [hiL] at hL3; exact absurd hL3 (by decide)
  ·
    have hLV : L = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hV16, hiL]; norm_num)
    have hvL : v ∈ L := hLV ▸ hv
    rw [hkb v hvL.2, hkb v hvL.2]

omit [Finite G] in
theorem exists_mem_alternatingGroup_orderOf_four :
    ∃ σ : alternatingGroup (Fin 6), orderOf σ = 2 ^ 2 := by
  refine ⟨⟨Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1 * Equiv.swap 4 5, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    simp [Equiv.Perm.sign_mul]
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)

@[expose] noncomputable def sec2KAction (E F : Subgroup G) (e : ↥(sec2PlanesP E F) ≃ Fin 6) :
    ↥(sec2K E) →* alternatingGroup (Fin 6) :=
  ((sec2PlanesActionFin E F e).comp (inclusion (sec2K_le_normalizer_sec2P E))).codRestrict _
    fun k => mem_alternatingGroup_of_mem_sec2K e k.2

omit [Finite G] in
theorem coe_sec2KAction_apply (E F : Subgroup G) (e : ↥(sec2PlanesP E F) ≃ Fin 6)
    (k : ↥(sec2K E)) :
    (sec2KAction E F e k : Equiv.Perm (Fin 6)) =
      sec2PlanesActionFin E F e ⟨k, sec2K_le_normalizer_sec2P E k.2⟩ :=
  rfl

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
  (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F))) (e : ↥(sec2PlanesP E F) ≃ Fin 6)

include h11 hE16 hF hL hodd hx hxS h4

theorem sec2KAction_surjective : Function.Surjective (sec2KAction E F e) := by
  intro σ
  obtain ⟨k, hk, hkσ⟩ :=
    exists_mem_sec2K_eq_of_mem_alternatingGroup h11 hE16 hF hL hodd hx hxS h4 e σ.2
  exact ⟨⟨k, hk⟩, Subtype.ext hkσ⟩

variable {rep : Fin 64 → G} {ψ : ↥(normalizer (sec2P E : Set G)) →* Equiv.Perm (Fin 64)}
  (hc : Sec2HexaCoord E A F rep e ψ)

include hc

theorem mem_centralizerMod_iff_psi {n : ↥(normalizer (sec2P E : Set G))}
    (hnK : (n : G) ∈ sec2K E) :
    (n : G) ∈ centralizerMod (sec2K E) (sec2P E) (E ⊓ A) ↔ ψ n = 1 := by
  rw [mem_centralizerMod, ← inv_eq_one, ← map_inv,
    psi_eq_one_iff h11 hE16 hF hL hodd hx hxS h4 hc]
  constructor
  · rintro ⟨-, -, h⟩ p hp
    have := h p hp
    simpa [mul_assoc] using this
  · intro h
    refine ⟨hnK, normalizer_sec2P_le_normalizer_inf h11 hE16 hF hL hodd hx hxS h4 n.2,
      fun p hp => ?_⟩
    have := h p hp
    simpa [mul_assoc] using this

theorem sec2KAction_eq_one_of_mem_centralizer {k : ↥(sec2K E)}
    (hk : (k : G) ∈ centralizer ((E ⊓ A : Subgroup G) : Set G)) : sec2KAction E F e k = 1 := by
  have hsimp : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hsurj := sec2KAction_surjective h11 hE16 hF hL hodd hx hxS h4 e
  have hNP := normalizer_sec2P_le_normalizer_inf h11 hE16 hF hL hodd hx hxS h4
  set D := (sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)).subgroupOf (sec2K E) with hD
  have hDn : D.Normal := by
    refine ⟨fun n hn l => ?_⟩
    rw [hD, mem_subgroupOf] at hn ⊢
    refine Subgroup.mem_inf.mpr ⟨(l * n * l⁻¹).2, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hlN := hNP (sec2K_le_normalizer_sec2P E l.2)
    have hw' : (l : G)⁻¹ * w * l ∈ E ⊓ A := by
      have := (mem_normalizer_iff.mp (inv_mem hlN) w).mp hw
      simpa using this
    have h1 := mem_centralizer_iff.mp hn.2 _ hw'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc w * (l * n * (l : G)⁻¹) = l * (((l : G)⁻¹ * w * l) * n) * (l : G)⁻¹ := by group
      _ = l * (n * ((l : G)⁻¹ * w * l)) * (l : G)⁻¹ := by rw [h1]
      _ = l * n * (l : G)⁻¹ * w := by group
  have hDφ : (D.map (sec2KAction E F e)).Normal := hDn.map _ hsurj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map (sec2KAction E F e)) with h | h
  · have hmem : sec2KAction E F e k ∈ D.map (sec2KAction E F e) :=
      ⟨k, show k ∈ D by rw [hD, mem_subgroupOf]; exact Subgroup.mem_inf.mpr ⟨k.2, hk⟩, rfl⟩
    rw [h] at hmem
    exact hmem
  · exfalso
    obtain ⟨a, ha, ⟨j, hj⟩, haP, hρ⟩ := exists_five_element h11 hE16 hF hL hodd hx hxS h4 e
    have hodd' : Odd (orderOf a) := by
      obtain ⟨i, -, hi⟩ :=
        (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one hj)
      rw [hi]
      exact Odd.pow (by decide)
    have haK : a ∈ sec2K E := mem_sec2K_of_odd haP hodd'
    have hmem : sec2KAction E F e ⟨a, haK⟩ ∈ D.map (sec2KAction E F e) := h ▸ mem_top _
    obtain ⟨m, hmD, hm⟩ := hmem
    replace hmD : m ∈ D := hmD
    rw [hD, mem_subgroupOf] at hmD
    have hmP := sec2K_le_normalizer_sec2P E m.2
    set n : ↥(normalizer (sec2P E : Set G)) := ⟨a * (m : G)⁻¹, mul_mem haP (inv_mem hmP)⟩
      with hn
    have hnG : (n : G) = a * (m : G)⁻¹ := rfl
    have hρn : sec2PlanesActionFin E F e n = 1 := by
      have h1 : sec2PlanesActionFin E F e ⟨m, hmP⟩ = sec2PlanesActionFin E F e ⟨a, haP⟩ :=
        congrArg Subtype.val hm
      have h2 : n = ⟨a, haP⟩ * (⟨m, hmP⟩ : ↥(normalizer (sec2P E : Set G)))⁻¹ := Subtype.ext rfl
      rw [h2, map_mul, map_inv, ← h1, mul_inv_cancel]
    have hω3 : omegaPerm ^ 3 = 1 := by rw [pow_succ, pow_two]; exact omegaPerm_cube
    have hψ3 : ψ (n ^ 3) = 1 := by
      rw [map_pow]
      rcases psi_eq_of_mem_ker h11 hE16 hF hL hodd hc n hρn with h' | h' | h'
      · rw [h', one_pow]
      · rw [h', hω3]
      · rw [h', ← sq, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
    have hn3K : ((n ^ 3 : ↥(normalizer (sec2P E : Set G))) : G) ∈ sec2K E := by
      rw [Subgroup.coe_pow]
      exact pow_mem (mul_mem haK (inv_mem m.2)) 3
    have hn3C := centralizerMod_le_centralizer h11 hE16 hF hL hodd hx hxS h4
      ((mem_centralizerMod_iff_psi h11 hE16 hF hL hodd hx hxS h4 e hc hn3K).mpr hψ3)
    rw [Subgroup.coe_pow] at hn3C
    have hconj : ∀ i : ℕ, ∀ w ∈ E ⊓ A,
        a ^ i * w * (a ^ i)⁻¹ = (n : G) ^ i * w * ((n : G) ^ i)⁻¹ := by
      intro i
      induction i with
      | zero => intro w _; simp
      | succ i ih =>
        intro w hw
        have hw' : (n : G) ^ i * w * ((n : G) ^ i)⁻¹ ∈ E ⊓ A :=
          (mem_normalizer_iff.mp (pow_mem (hNP n.2) i) w).mp hw
        have hmw := mem_centralizer_iff.mp hmD.2 _ hw'
        have ha_eq : a = (n : G) * m := by rw [hnG]; group
        calc a ^ (i + 1) * w * (a ^ (i + 1))⁻¹ = a * (a ^ i * w * (a ^ i)⁻¹) * a⁻¹ := by
              rw [pow_succ']; group
          _ = a * ((n : G) ^ i * w * ((n : G) ^ i)⁻¹) * a⁻¹ := by rw [ih w hw]
          _ = (n : G) * (m * ((n : G) ^ i * w * ((n : G) ^ i)⁻¹) * (m : G)⁻¹) * (n : G)⁻¹ := by
              rw [ha_eq]; group
          _ = (n : G) * (((n : G) ^ i * w * ((n : G) ^ i)⁻¹) * m * (m : G)⁻¹) * (n : G)⁻¹ := by
              rw [← hmw]
          _ = (n : G) ^ (i + 1) * w * ((n : G) ^ (i + 1))⁻¹ := by
              rw [pow_succ' (n : G) i]; group
    have ha3 : ∀ w ∈ E ⊓ A, a ^ 3 * w * (a ^ 3)⁻¹ = w := fun w hw => by
      rw [hconj 3 w hw]
      have h1 := mem_centralizer_iff.mp hn3C w hw
      calc (n : G) ^ 3 * w * ((n : G) ^ 3)⁻¹ = w * (n : G) ^ 3 * ((n : G) ^ 3)⁻¹ := by rw [h1]
        _ = w := by group
    have ha1 : ∀ w ∈ E ⊓ A, a * w * a⁻¹ = w := fun w hw => by
      have hcop : Nat.Coprime 3 (5 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
      have hab := Nat.gcd_eq_gcd_ab 3 (5 ^ j)
      rw [hcop.gcd_eq_one, Nat.cast_one] at hab
      have ha' : a = (a ^ 3) ^ (Nat.gcdA 3 (5 ^ j)) * (a ^ 5 ^ j) ^ (Nat.gcdB 3 (5 ^ j)) := by
        rw [← zpow_natCast a 3, ← zpow_natCast a (5 ^ j), ← zpow_mul, ← zpow_mul, ← zpow_add,
          ← hab, zpow_one]
      rw [hj, one_zpow, mul_one] at ha'
      have hc3 : a ^ 3 ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr (by
        have h1 := ha3 w hw
        calc a ^ 3 * w = a ^ 3 * w * (a ^ 3)⁻¹ * a ^ 3 := by group
          _ = w * a ^ 3 := by rw [h1])
      have hca : a ∈ centralizer ({w} : Set G) := by
        rw [ha']
        exact zpow_mem hc3 _
      have h2 := mem_centralizer_singleton_iff.mp hca
      calc a * w * a⁻¹ = w * a * a⁻¹ := by rw [h2]
        _ = w := by group
    have hne : ∃ w ∈ E ⊓ A, w ≠ 1 := by
      by_contra hall
      push Not at hall
      have hbot : E ⊓ A = ⊥ := eq_bot_iff.mpr fun w hw => hall w hw
      have h16 := card_inf_left hF hodd
      rw [hbot, card_bot] at h16
      norm_num at h16
    obtain ⟨w, hw, hw1⟩ := hne
    exact hw1 (eq_one_of_conj_eq_of_five h11 hE16 hF hL hodd hx hxS e ha.1 hj haP hρ hw
      (ha1 w hw))

omit hc in
theorem exists_two_element : ∃ k : ↥(sec2K E), (∃ j : ℕ, k ^ 2 ^ j = 1) ∧
    sec2KAction E F e (k ^ 2) ≠ 1 := by
  obtain ⟨σ, hσ⟩ := exists_mem_alternatingGroup_orderOf_four
  obtain ⟨k₀, hk₀⟩ := sec2KAction_surjective h11 hE16 hF hL hodd hx hxS h4 e σ
  obtain ⟨y, hy, hy2, w, hw, hwo, hyw⟩ := exists_two_mul_odd k₀
  have hφw : sec2KAction E F e w = 1 := by
    obtain ⟨z, rfl⟩ := mem_zpowers_iff.mp hw
    have h1 : orderOf (sec2KAction E F e (k₀ ^ z)) ∣ orderOf (k₀ ^ z) := orderOf_map_dvd _ _
    have h2 : orderOf (sec2KAction E F e (k₀ ^ z)) ∣ 2 ^ 2 := by
      rw [map_zpow, hk₀, ← hσ]
      exact orderOf_dvd_of_mem_zpowers (zpow_mem_zpowers σ z)
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have h3 : orderOf (sec2KAction E F e (k₀ ^ z)) = 1 := by
      rw [hi'] at h1 ⊢
      rcases i with _ | i
      · rfl
      · exfalso
        have h4' : Odd (2 ^ (i + 1)) := hwo.of_dvd_nat h1
        exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero i⟩)) h4'
    exact orderOf_eq_one_iff.mp h3
  have hφy : sec2KAction E F e y = σ := by
    have : y = k₀ * w⁻¹ := by rw [hyw]; group
    rw [this, map_mul, map_inv, hφw, inv_one, mul_one, hk₀]
  obtain ⟨j, hj⟩ := hy2.exists_card_eq
  rw [Nat.card_zpowers] at hj
  refine ⟨y, ⟨j, by rw [← hj]; exact pow_orderOf_eq_one y⟩, ?_⟩
  rw [map_pow, hφy]
  intro h1
  have := orderOf_dvd_of_pow_eq_one h1
  rw [hσ] at this
  norm_num at this

theorem mem_centralizer_of_sec2KAction_eq_one {t : ↥(sec2K E)} (ht : sec2KAction E F e t = 1) :
    (t : G) ∈ centralizer ((E ⊓ A : Subgroup G) : Set G) := by
  have hNP := normalizer_sec2P_le_normalizer_inf h11 hE16 hF hL hodd hx hxS h4
  have htP := sec2K_le_normalizer_sec2P E t.2
  set tN : ↥(normalizer (sec2P E : Set G)) := ⟨t, htP⟩ with htN
  have hρt : sec2PlanesActionFin E F e tN = 1 := congrArg Subtype.val ht
  have hω3 : omegaPerm ^ 3 = 1 := by rw [pow_succ, pow_two]; exact omegaPerm_cube
  have hCK := centralizerMod_le_centralizer h11 hE16 hF hL hodd hx hxS h4
  have hmemC := fun {n : ↥(normalizer (sec2P E : Set G))} (hnK : (n : G) ∈ sec2K E) =>
    (mem_centralizerMod_iff_psi h11 hE16 hF hL hodd hx hxS h4 e hc hnK).mpr
  have ht3 : ∀ w ∈ E ⊓ A, (t : G) ^ 3 ^ 1 * w * ((t : G) ^ 3 ^ 1)⁻¹ = w := by
    have hψ3 : ψ (tN ^ 3) = 1 := by
      rw [map_pow]
      rcases psi_eq_of_mem_ker h11 hE16 hF hL hodd hc tN hρt with h' | h' | h'
      · rw [h', one_pow]
      · rw [h', hω3]
      · rw [h', ← sq, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
    have hK3 : ((tN ^ 3 : ↥(normalizer (sec2P E : Set G))) : G) ∈ sec2K E := by
      rw [Subgroup.coe_pow]
      exact pow_mem t.2 3
    have h3 : (t : G) ^ 3 ∈ centralizer ((E ⊓ A : Subgroup G) : Set G) := by
      have h3' := hCK (hmemC hK3 hψ3)
      rwa [Subgroup.coe_pow] at h3'
    intro w hw
    rw [pow_one, ← mem_centralizer_iff.mp h3 w hw]
    group
  have hcomm : ∀ k ∈ sec2K E, ∀ w ∈ E ⊓ A,
      (t : G) * (k * w * k⁻¹) * (t : G)⁻¹ = k * ((t : G) * w * (t : G)⁻¹) * k⁻¹ := by
    intro k hk w hw
    have hkP := sec2K_le_normalizer_sec2P E hk
    have hψ := psi_commute_of_mem_sec2K h11 hE16 hF hL hodd hc tN hρt hk
    set kN : ↥(normalizer (sec2P E : Set G)) := ⟨k, hkP⟩ with hkN
    set d : ↥(normalizer (sec2P E : Set G)) := tN⁻¹ * kN⁻¹ * tN * kN with hd
    have hdψ : ψ d = 1 := by
      rw [hd, map_mul, map_mul, map_mul, map_inv, map_inv]
      have e1 : (ψ tN)⁻¹ * (ψ kN)⁻¹ * ψ tN * ψ kN = (ψ tN)⁻¹ * (ψ kN)⁻¹ * (ψ tN * ψ kN) := by
        group
      rw [e1, ← hψ]
      group
    have hdK : (d : G) ∈ sec2K E := by
      rw [hd]
      exact mul_mem (mul_mem (mul_mem (inv_mem t.2) (inv_mem hk)) t.2) hk
    have hdC := hCK (hmemC hdK hdψ)
    have hdG : (d : G) = (t : G)⁻¹ * k⁻¹ * t * k := rfl
    have hdw := mem_centralizer_iff.mp hdC w hw
    calc (t : G) * (k * w * k⁻¹) * (t : G)⁻¹ = k * t * (d * w) * (d : G)⁻¹ * (t : G)⁻¹ * k⁻¹ := by
          rw [hdG]; group
      _ = k * t * (w * d) * (d : G)⁻¹ * (t : G)⁻¹ * k⁻¹ := by rw [hdw]
      _ = k * ((t : G) * w * (t : G)⁻¹) * k⁻¹ := by group
  by_contra hnot
  have hWK : sec2K E ≤ normalizer
      (((E ⊓ A) ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) : Set G) := fun k hk =>
    Sec2.mem_normalizer_of_forall_conj_mem fun w hw => by
      have hkw : k * w * k⁻¹ ∈ E ⊓ A :=
        (mem_normalizer_iff.mp (hNP (sec2K_le_normalizer_sec2P E hk)) w).mp hw.1
      refine Subgroup.mem_inf.mpr ⟨hkw, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := hcomm k hk w hw.1
      have h2 : (t : G) * w * (t : G)⁻¹ = w := by
        rw [← mem_centralizer_singleton_iff.mp hw.2]
        group
      rw [h2] at h1
      calc k * w * k⁻¹ * t = (t : G) * (k * w * k⁻¹) * (t : G)⁻¹ * t := by rw [h1]
        _ = t * (k * w * k⁻¹) := by group
  rcases eq_bot_or_eq_of_le_inf h11 hE16 hF hL hodd hx hxS h4 inf_le_left hWK with hW1 | hW1
  · have htfix : ∀ w ∈ E ⊓ A, (t : G) * w * (t : G)⁻¹ = w → w = 1 := fun w hw h => by
      have hwW : w ∈ (E ⊓ A) ⊓ centralizer ({(t : G)} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hw, mem_centralizer_singleton_iff.mpr (by
        calc w * t = (t : G) * w * (t : G)⁻¹ * t := by rw [h]
          _ = t * w := by group)⟩
      rw [hW1] at hwW
      exact hwW
    obtain ⟨k, ⟨j, hj⟩, hk2⟩ := exists_two_element h11 hE16 hF hL hodd hx hxS h4 e
    obtain ⟨hEe, -⟩ := isElemAbelian_and_card_of_mem_planes hF
      (⟨1, Or.inl (rightConjugate_one E).symm⟩ : E ∈ planes E F)
    have hab : ∀ v ∈ E ⊓ A, ∀ w ∈ E ⊓ A, v * w = w * v := fun v hv w hw =>
      congrArg Subtype.val (hEe.1.is_comm.comm ⟨v, hv.1⟩ ⟨w, hw.1⟩)
    have h2 : ∀ v ∈ E ⊓ A, v * v = 1 := fun v hv => by rw [← sq]; exact hEe.2 v hv.1
    have hkG : (k : G) ^ 2 ^ j = 1 := by rw [← Subgroup.coe_pow, hj, OneMemClass.coe_one]
    have hsq := fun {v : G} (hv : v ∈ E ⊓ A) => conj_sq_eq_of_fpf hab h2 (card_inf_left hF hodd)
      (hNP htP) (hNP (sec2K_le_normalizer_sec2P E k.2)) ht3 htfix (hcomm k k.2) hkG hv
    have hk2C : ((k ^ 2 : ↥(sec2K E)) : G) ∈ centralizer ((E ⊓ A : Subgroup G) : Set G) :=
      mem_centralizer_iff.mpr fun v hv => by
        rw [Subgroup.coe_pow]
        have h1 := hsq hv
        calc v * (k : G) ^ 2 = (k : G) * (k * v * (k : G)⁻¹) * (k : G)⁻¹ * (k : G) ^ 2 := by
              rw [h1]
          _ = (k : G) ^ 2 * v := by rw [sq]; group
    exact hk2 (sec2KAction_eq_one_of_mem_centralizer h11 hE16 hF hL hodd hx hxS h4 e hc hk2C)
  · apply hnot
    refine mem_centralizer_iff.mpr fun w hw => ?_
    rw [← hW1] at hw
    exact (mem_centralizer_singleton_iff.mp hw.2)

end Frame

end CFSG.ComponentClassification.AS81

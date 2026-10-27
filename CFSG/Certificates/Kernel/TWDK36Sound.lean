module

public import CFSG.Certificates.Kernel.TWDKSound
public import CFSG.LocalAnalysis.StandardType.GGTWDNat36Out
public import Certificates.Data.Kernel.TWDK36

public section

namespace CFSG.StandardType.TWDK36

open Certificates.TWDK Certificates.TWDK36 Certificates.DepASmall Certificates.TwoDepSmall
open Certificates.TwoDepSmallN CFSG.StandardType CFSG.StandardType.TWDK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ}

theorem form_apply (f v : GGDepAE p N) : ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot, smul_eq_mul]

theorem twDual (f : GGDepAE p N) (e : Module.End (ZMod p) (GGDepAE p N)) :
    ∃ f' : GGDepAE p N, ∀ v, ggDepAdot f' v = ggDepAdot f (e v) := by
  refine ⟨fun j => ggDepAdot f (e (Pi.single j 1)), fun v => ?_⟩
  have hv : v = ∑ j, v j • (Pi.single j (1 : ZMod p) : GGDepAE p N) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  calc ggDepAdot (fun j => ggDepAdot f (e (Pi.single j 1))) v
      = ∑ j, v j * ggDepAdot f (e (Pi.single j 1)) := by
        simp only [ggDepAdot]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = ggDepAform f (e (∑ j, v j • (Pi.single j (1 : ZMod p) : GGDepAE p N))) := by
        rw [map_sum, map_sum]
        simp only [map_smul, form_apply, smul_eq_mul]
    _ = ggDepAdot f (e v) := by rw [← hv, form_apply]

theorem twE_x (hN : 1 ≤ N) {e d : Module.End (ZMod p) (GGDepAE p N)} (hde : d * e = 1)
    (hd0 : ∀ f : GGDepAE p N, vAt f (N - 1) = 0 → ∀ v, ggDepAdot f (d v) = ggDepAdot f v) :
    ∃ c : ZMod p, e (ggDepAx p N) = c • ggDepAx p N := by
  refine ⟨e (ggDepAx p N) ⟨N - 1, by omega⟩, ?_⟩
  funext j
  by_cases hj : j.val + 1 = N
  · have hj' : j = ⟨N - 1, by omega⟩ := Fin.ext (by change j.val = N - 1; omega)
    rw [hj']
    simp [ggDepAx, Nat.sub_add_cancel hN]
  · have h0 : vAt (Pi.single j (1 : ZMod p) : GGDepAE p N) (N - 1) = 0 := by
      rw [vAt_lt _ (by omega : N - 1 < N)]
      rw [Pi.single_apply, if_neg (fun h => hj (by rw [← h, Fin.val_mk]; omega))]
    have h := hd0 _ h0 (e (ggDepAx p N))
    rw [twApply_of_mul hde, twDot_single_left, twDot_single_left] at h
    rw [Pi.smul_apply, smul_eq_mul, ← h]
    simp [ggDepAx, hj]

theorem twRefl_conj {e d : Module.End (ZMod p) (GGDepAE p N)} (hde : d * e = 1)
    (c f f' : GGDepAE p N) (hf : ∀ v, ggDepAdot f' v = ggDepAdot f (e v)) :
    d * ggDepARefl c f * e = ggDepARefl (d c) f' := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, l05nPT_refl_apply, map_sub, map_smul, hf,
    twApply_of_mul hde]

@[expose] def twC {e d : Module.End (ZMod p) (GGDepAE p N)} (hed : e * d = 1) (hde : d * e = 1) :
    Module.End (ZMod p) (GGDepAE p N) →* Module.End (ZMod p) (GGDepAE p N) where
  toFun s := d * s * e
  map_one' := by simp only [mul_one, hde]
  map_mul' s t := by
    simp only [mul_assoc]
    rw [← mul_assoc e d (t * e), hed, one_mul]

theorem twC_apply {e d : Module.End (ZMod p) (GGDepAE p N)} (hed : e * d = 1) (hde : d * e = 1)
    (s : Module.End (ZMod p) (GGDepAE p N)) : twC hed hde s = d * s * e := rfl

theorem twC_back {e d : Module.End (ZMod p) (GGDepAE p N)} (hed : e * d = 1)
    (s : Module.End (ZMod p) (GGDepAE p N)) : e * (d * s * e) * d = s := by
  have h : e * (d * s * e) * d = (e * d) * s * (e * d) := by simp only [mul_assoc]
  rw [h, hed, one_mul, mul_one]

theorem e6_back {e d : Module.End (ZMod 3) (GGDepAE 3 6)} (hed : e * d = 1) (hde : d * e = 1)
    (hex : ∃ c : ZMod 3, e (ggDepAx 3 6) = c • ggDepAx 3 6)
    {T T' : Set (Module.End (ZMod 3) (GGDepAE 3 6))}
    (hT : ∀ s ∈ T', d * s * e ∈ Submonoid.closure T)
    (hT' : ∀ g ∈ T, e * g * d ∈ Submonoid.closure T') (h : GGTWDE6Orbit T') :
    GGTWDE6Orbit T := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨s, w, hrefl, hsT, hgS, hcox, hwT, hinj⟩ := h
  obtain ⟨c, hc⟩ := hex
  have hle : Submonoid.closure T' ≤ (Submonoid.closure T).comap (twC hed hde) :=
    Submonoid.closure_le.mpr fun s hs => hT s hs
  have hle' : Submonoid.closure T' ≤ Submonoid.closure (Set.range s) :=
    Submonoid.closure_le.mpr hgS
  have hleS : Submonoid.closure (Set.range s) ≤
      (Submonoid.closure (Set.range fun i => twC hed hde (s i))).comap (twC hed hde) :=
    Submonoid.closure_le.mpr fun _ ⟨i, hi⟩ => by
      rw [← hi]
      exact Submonoid.subset_closure ⟨i, rfl⟩
  have hx0 : ggDepAx 3 6 ≠ 0 := fun h0 => by
    have := congrFun h0 ⟨5, by norm_num⟩
    simp [ggDepAx] at this
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, zero_smul] at hc
    apply hx0
    rw [← twApply_of_mul hde (ggDepAx 3 6), hc, map_zero]
  refine ⟨fun i => twC hed hde (s i), fun k => twC hed hde (w k), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨c', f, hfc, hs⟩ := hrefl i
    obtain ⟨f', hf'⟩ := twDual f e
    refine ⟨d c', f', ?_, ?_⟩
    · rw [hf', twApply_of_mul hed, hfc]
    · change d * s i * e = _
      rw [hs, twRefl_conj hde c' f f' hf']
  · intro i
    exact hle (hsT i)
  · intro g hg
    have h1 := hleS (hle' (hT' g hg))
    rw [Submonoid.mem_comap, twC_apply, twC_back hde] at h1
    exact h1
  · intro i j
    change (twC hed hde (s i) * twC hed hde (s j)) ^ _ = 1
    rw [← map_mul, ← map_pow, hcox, map_one]
  · intro k
    exact hle (hwT k)
  · intro k j hkj
    simp only [twC_apply, Module.End.mul_apply, hc, map_smul] at hkj
    have h1 := smul_right_injective _ hc0 hkj
    apply hinj
    change w k (ggDepAx 3 6) = w j (ggDepAx 3 6)
    rw [← twApply_of_mul hed (w k _), ← twApply_of_mul hed (w j _)]
    exact congrArg e h1

@[expose] def OutBack (Out : Set (Module.End (ZMod p) (GGDepAE p N)) → Prop) : Prop :=
  ∀ (e d : Module.End (ZMod p) (GGDepAE p N)) (T T' : Set (Module.End (ZMod p) (GGDepAE p N))),
    e * d = 1 → d * e = 1 → (∃ c : ZMod p, e (ggDepAx p N) = c • ggDepAx p N) →
      (∀ s ∈ T', d * s * e ∈ Submonoid.closure T) →
        (∀ g ∈ T, e * g * d ∈ Submonoid.closure T') → Out T' → Out T

theorem e6_outBack : OutBack (p := 3) (N := 6) GGTWDE6Orbit :=
  fun _ _ _ _ hed hde hex hT hT' h => e6_back hed hde hex hT hT' h

abbrev frameR (p N : ℕ) : Set (Module.End (ZMod p) (GGDepAE p N)) :=
  Set.range (fun i : Fin (N - 1) => ggDepARefl (ggDepAh p N i) (ggDepAα p N i))

theorem or_back {Out : Set (Module.End (ZMod p) (GGDepAE p N)) → Prop} (hOut : OutBack Out)
    {e d : Module.End (ZMod p) (GGDepAE p N)} (hed : e * d = 1) (hde : d * e = 1)
    (hfr : ∀ i : Fin (N - 1), d * ggDepARefl (ggDepAh p N i) (ggDepAα p N i) * e =
      ggDepARefl (ggDepAh p N i) (ggDepAα p N i))
    (hex : ∃ c : ZMod p, e (ggDepAx p N) = c • ggDepAx p N)
    {news : List GGDepANPair} {X : Set (Module.End (ZMod p) (GGDepAE p N))}
    (hq : ∀ q ∈ news, d * ggTWDRflOf p N q * e ∈ X)
    (hX : ∀ g ∈ X, ∃ q ∈ news, g = d * ggTWDRflOf p N q * e)
    (h : (∃ g ∈ Submonoid.closure (ggTWDGens p N news), GGDepAIsTv g) ∨
      Out (ggTWDGens p N news)) :
    (∃ g ∈ Submonoid.closure (frameR p N ∪ X), GGDepAIsTv g) ∨ Out (frameR p N ∪ X) := by
  rcases h with h | h
  · exact Or.inl (tv_back_gens hed hde hfr Set.subset_union_left
      (fun q hq' => Or.inr (hq q hq')) h)
  · refine Or.inr (hOut e d _ _ hed hde hex ?_ ?_ h)
    · rintro s (⟨i, rfl⟩ | ⟨q, hq', rfl⟩)
      · rw [hfr i]
        exact Submonoid.subset_closure (Or.inl ⟨i, rfl⟩)
      · exact Submonoid.subset_closure (Or.inr (hq q hq'))
    · rintro g (⟨i, rfl⟩ | hg)
      · have h := twC_back hed (ggDepARefl (ggDepAh p N i) (ggDepAα p N i))
        rw [hfr i] at h
        change e * ggDepARefl (ggDepAh p N i) (ggDepAα p N i) * d ∈ _
        rw [h]
        exact Submonoid.subset_closure (Or.inl ⟨i, rfl⟩)
      · obtain ⟨q, hq', rfl⟩ := hX g hg
        rw [twC_back hed]
        exact Submonoid.subset_closure (Or.inr ⟨q, hq', rfl⟩)

theorem kSolC_length (pos code a b t : ℕ) : (kSolC p N pos code a b t).length = N := by
  unfold kSolC; split_ifs <;> exact kVec_length _ _ _ _ _ _

theorem kANC_length (pos code u : ℕ) : (kANC p N pos code u).length = N := by
  unfold kANC; split_ifs <;> exact kAN_length _ _ _ _

theorem kBond_lt [Fact p.Prime] (code : ℕ) : kBond p code < p := by
  unfold kBond; split_ifs
  · exact twMod_lt _
  · exact (Fact.out : p.Prime).pos

theorem kBond_cast [Fact p.Prime] (c₂ : Option (Fin (N - 1))) :
    ((kBond p (ggTWNCode (c₂.map Fin.val)) : ℕ) : ZMod p) = if c₂ = none then -1 else 0 := by
  cases c₂ with
  | none => simpa [kBond, ggTWNCode] using twCast_neg_one (p := p)
  | some c' => simp [kBond, ggTWNCode]

theorem mem_kOuterA {pos c a b t u : ℕ} (ha : a < p) (hb : b < p) (ht : t < p) (hu : u < p)
    (hd : ggDepANDot p (kAN p N pos c ((p - 1) % p) u)
      (kVec p N pos c ((p - 1) % p) a b t) = 2 % p) :
    (kVec p N pos c ((p - 1) % p) a b t, kAN p N pos c ((p - 1) % p) u) ∈ kOuterA p N pos c := by
  simp only [kOuterA, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  exact ⟨a, ha, b, hb, t, ht, u, hu, by rw [if_pos (beq_iff_eq.mpr hd)]⟩

theorem mem_kA2All {pos code a b t : ℕ} (ha : a < p) (hb : b < p) (ht : t < p) :
    kSolC p N pos code a b t ∈ kA2All p N pos code := by
  simp only [kA2All, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨a, ha, b, hb, t, ht, rfl⟩

theorem mem_kA2Norm {pos code u : ℕ} (hu : u < p) : kANC p N pos code u ∈ kA2Norm p N pos code :=
  List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩

theorem mem_kInnerC {pos code : ℕ} {as2 : List (List ℕ)} {o : GGDepANPair} {a b t : ℕ}
    {a2 : List ℕ} (ha : a < p) (hb : b < p) (ht : t < p)
    (h1 : ggDepANDot p o.2 (kSolC p N pos code a b t) = kBond p code) (hmem : a2 ∈ as2)
    (h2 : ggDepANDot p a2 (kSolC p N pos code a b t) = 2 % p)
    (h3 : ggDepANDot p a2 o.1 = kBond p code) :
    (kSolC p N pos code a b t, a2) ∈ kInnerC p N pos code as2 o := by
  simp only [kInnerC, List.mem_flatMap, List.mem_range]
  refine ⟨a, ha, b, hb, t, ht, ?_⟩
  rw [if_pos (beq_iff_eq.mpr h1), List.mem_filterMap]
  exact ⟨a2, hmem, by rw [h2, h3]; simp⟩

theorem chainH2 (hN : 5 ≤ N) (pos : GGTWPos) (c₂ : Option (Fin (N - 1))) (v : GGDepAE p N)
    (hv : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot (ggDepAα p N c) v = if some c = c₂ then -1 else 0) :
    ∀ k, kChain N (ggTWPosNat pos) k = true → kChain N (ggTWPosNat pos) (k + 1) = true →
      vAt v k - vAt v (k + 1) = if some k = c₂.map Fin.val then -1 else 0 := by
  intro k h1 h2
  obtain ⟨hJ, hk⟩ := twInJ_of_chain hN pos k h1 h2
  have := hv ⟨k, by omega⟩ hJ
  rw [twDot_A_short v ⟨k, by omega⟩ hk] at this
  rw [this]
  cases c₂ with
  | none => simp
  | some c' => simp [Fin.ext_iff]

theorem chainA2 (hN : 5 ≤ N) (pos : GGTWPos) (c₂ : Option (Fin (N - 1))) (v : GGDepAE p N)
    (hv : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot v (ggDepAh p N c) = if some c = c₂ then -1 else 0) :
    ∀ k, kChain N (ggTWPosNat pos) k = true → kChain N (ggTWPosNat pos) (k + 1) = true →
      vAt v k - vAt v (k + 1) = if some k = c₂.map Fin.val then -1 else 0 := by
  intro k h1 h2
  obtain ⟨hJ, hk⟩ := twInJ_of_chain hN pos k h1 h2
  have := hv ⟨k, by omega⟩ hJ
  rw [twDot_h_short v ⟨k, by omega⟩ hk] at this
  rw [this]
  cases c₂ with
  | none => simp
  | some c' => simp [Fin.ext_iff]

theorem kSolC_complete [Fact p.Prime] (hN : 5 ≤ N) (pos : GGTWPos) (c₂ : Option (Fin (N - 1)))
    (hc₂ : ∀ c' : Fin (N - 1), c₂ = some c' → kLo pos ≤ c'.val) (v : GGDepAE p N)
    (h : ∀ k, kChain N (ggTWPosNat pos) k = true → kChain N (ggTWPosNat pos) (k + 1) = true →
      vAt v k - vAt v (k + 1) = if some k = c₂.map Fin.val then -1 else 0) :
    ggDepANToZ p N (kSolC p N (ggTWPosNat pos) (ggTWNCode (c₂.map Fin.val))
      (vAt v (kNc N pos)).val (vAt v (kLo pos)).val (vAt v (N - 1)).val) = v := by
  cases c₂ with
  | none =>
    simp only [kSolC, Option.map_none, ggTWNCode, if_true]
    exact kVec_complete hN pos 0 0 v (Or.inr Nat.cast_zero) fun k h1 h2 => by
      rw [h k h1 h2]; simp
  | some c' =>
    simp only [kSolC, Option.map_some, ggTWNCode, Nat.add_one_ne_zero, if_false,
      Nat.add_sub_cancel]
    exact kVec_complete hN pos c'.val ((p - 1) % p) v (Or.inl (hc₂ c' rfl)) fun k h1 h2 => by
      rw [h k h1 h2, twCast_neg_one]; simp

theorem kANC_complete [Fact p.Prime] (hN : 5 ≤ N) (pos : GGTWPos) (c₂ : Option (Fin (N - 1)))
    (hc₂ : ∀ c' : Fin (N - 1), c₂ = some c' → kLo pos ≤ c'.val) (v : GGDepAE p N)
    (h : ∀ k, kChain N (ggTWPosNat pos) k = true → kChain N (ggTWPosNat pos) (k + 1) = true →
      vAt v k - vAt v (k + 1) = if some k = c₂.map Fin.val then -1 else 0)
    (h0 : vAt v 0 = 0) (h1 : vAt v (N - 1) = 1) :
    ∃ u < p, ggDepANToZ p N (kANC p N (ggTWPosNat pos) (ggTWNCode (c₂.map Fin.val)) u) = v := by
  cases c₂ with
  | none =>
    simp only [kANC, Option.map_none, ggTWNCode, if_true]
    exact kAN_complete hN pos 0 0 v (Or.inr Nat.cast_zero) (fun k hk1 hk2 => by
      rw [h k hk1 hk2]; simp) h0 h1
  | some c' =>
    simp only [kANC, Option.map_some, ggTWNCode, Nat.add_one_ne_zero, if_false,
      Nat.add_sub_cancel]
    exact kAN_complete hN pos c'.val ((p - 1) % p) v (Or.inl (hc₂ c' rfl)) (fun k hk1 hk2 => by
      rw [h k hk1 hk2, twCast_neg_one]; simp) h0 h1

theorem one_of_cover36 {p' : ℕ} {F : List GGDepANPair} {O : List KOut} {S : List KOneE}
    {T : List KTwoE} (hC : kCover36 N S T = true)
    (hS : ∀ i < S.length, kOneAt p' N F O S i = true)
    (posn c0 mi ni : ℕ) (hpos : posn = 0 ∨ posn = 1) (hc0 : c0 < N - 1) (hmi : mi = 1 ∨ mi = 2)
    (hni : ni = 1 ∨ ni = 2) (hpat : ggTWNPat1B N posn c0 mi ni = true) :
    ∃ e : KOneE, e.1 = (posn, c0, mi, ni) ∧ kOne p' N F O e = true := by
  have h1 := List.all_eq_true.mp hC posn (by rcases hpos with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.mp h1 c0 (List.mem_range.mpr hc0)
  rw [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.mp h2.1 mi (by rcases hmi with rfl | rfl <;> simp)
  have h4 := List.all_eq_true.mp h3 ni (by rcases hni with rfl | rfl <;> simp)
  have h5 : (posn, c0, mi, ni) ∈ S.map (·.1) := by simpa [hpat] using h4
  obtain ⟨e, he, hek⟩ := List.mem_map.mp h5
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have h6 := hS i hi
  simp only [kOneAt, List.getElem?_eq_getElem hi] at h6
  exact ⟨_, hek, h6⟩

theorem two_of_cover36 {p' : ℕ} {F : List GGDepANPair} {O : List KOut} {S : List KOneE}
    {T : List KTwoE} (hC : kCover36 N S T = true)
    (hT : ∀ i < T.length, kTwoAt p' N F O T i = true)
    (posn c : ℕ) (c2 : Option ℕ) (hpos : posn = 0 ∨ posn = 1) (hc : c < N - 1)
    (hc2 : c2 ∈ none :: (List.range (N - 1)).map some)
    (hpat : ggTWNPat2B N posn c c2 = true) :
    ∃ e : KTwoE, e.1 = (posn, c, ggTWNCode c2) ∧ kTwo p' N F O e = true := by
  have h1 := List.all_eq_true.mp hC posn (by rcases hpos with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.mp h1 c (List.mem_range.mpr hc)
  rw [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.mp h2.2 c2 hc2
  have h5 : (posn, c, ggTWNCode c2) ∈ T.map (·.1) := by simpa [hpat] using h3
  obtain ⟨e, he, hek⟩ := List.mem_map.mp h5
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have h6 := hT i hi
  simp only [kTwoAt, List.getElem?_eq_getElem hi] at h6
  exact ⟨_, hek, h6⟩

variable [Fact p.Prime] {Out : Set (Module.End (ZMod p) (GGDepAE p N)) → Prop}
  {F : List GGDepANPair} {O : List KOut}

@[expose] def EntrySound (p N : ℕ) (F : List GGDepANPair) (O : List KOut)
    (Out : Set (Module.End (ZMod p) (GGDepAE p N)) → Prop) : Prop :=
  ∀ (news : List GGDepANPair) (ws : List KWit) (en : KE), (∀ q ∈ news, GGTWDValid p N q) →
    kTestE p N F O news ws en = true →
      (∃ g ∈ Submonoid.closure (ggTWDGens p N news), GGDepAIsTv g) ∨ Out (ggTWDGens p N news)

theorem outer_finish (hp2 : p ≠ 2) (hN : 5 ≤ N) (hE : EntrySound p N F O Out)
    (hOut : OutBack Out) (hF : kFrameOK p N F = true)
    {e d : Module.End (ZMod p) (GGDepAE p N)} (hed : e * d = 1) (hde : d * e = 1)
    (hfr : ∀ i : Fin (N - 1), d * ggDepARefl (ggDepAh p N i) (ggDepAα p N i) * e =
      ggDepARefl (ggDepAh p N i) (ggDepAα p N i))
    (hex : ∃ c : ZMod p, e (ggDepAx p N) = c • ggDepAx p N)
    {posn code : ℕ} {as2 : List (List ℕ)} {ws : List KWit} {os : List GGDepANPair}
    {ent : List (ℕ × List KE)} (hchk : kOuterOK p N F O posn code as2 ws os ent = true)
    {o c : GGDepANPair} (ho : o ∈ os) (hc : c ∈ kInnerC p N posn code as2 o)
    (hvo : GGTWDValid p N o) (hvc : GGTWDValid p N c)
    {X1 X2 : Module.End (ZMod p) (GGDepAE p N)}
    (hro : d * ggTWDRflOf p N o * e = X1) (hrc : d * ggTWDRflOf p N c * e = X2) :
    (∃ g ∈ Submonoid.closure (frameR p N ∪ {X1, X2}), GGDepAIsTv g) ∨
      Out (frameR p N ∪ {X1, X2}) := by
  unfold kOuterOK at hchk
  obtain ⟨en, hen⟩ := kAll2_mem _ _ ent hchk o ho
  try dsimp only at hen
  by_cases h0 : en.1 = 0
  · rw [if_pos h0] at hen
    obtain ⟨j, hj⟩ := kAll2_mem _ _ _ hen c hc
    try dsimp only at hj
    have hv : ∀ q ∈ [o, c], GGTWDValid p N q := by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hvo
      · exact hvc
    refine or_back hOut hed hde hfr hex ?_ ?_ (hE [o, c] ws j hv hj)
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · rw [hro]; exact Set.mem_insert _ _
      · rw [hrc]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    · intro g hg
      rcases hg with rfl | hg
      · exact ⟨o, by simp, hro.symm⟩
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact ⟨c, by simp, hrc.symm⟩
  · rw [if_neg h0] at hen
    have hv : ∀ q ∈ [o], GGTWDValid p N q := by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact hvo
    refine Or.inl (tv_back_gens hed hde hfr Set.subset_union_left ?_
      (kTest_sound hp2 hN hF hv _ hen))
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [hro]
    exact Or.inr (Set.mem_insert _ _)

theorem twdk36_cells1 (hp2 : p ≠ 2) (hpN : p ∣ N) (hN : 5 ≤ N) (hE : EntrySound p N F O Out)
    (hOut : OutBack Out) {S : List KOneE} {T : List KTwoE}
    (hF : kFrameOK p N F = true) (hC : kCover36 N S T = true)
    (hS : ∀ i < S.length, kOneAt p N F O S i = true) :
    ∀ (pos : GGTWPos) (c0 : Fin (N - 1)) (m n : ℤ), GGTWPat1 N pos c0.val m n →
      ∀ ha αa : GGDepAE p N, GGTWDPairs1 p N pos c0 m n ha αa → ggDepAdot αa ha = 2 →
        ggDepAdot αa (ggDepAx p N) ≠ 0 →
          (∃ g ∈ Submonoid.closure (frameR p N ∪ {ggDepARefl ha αa}), GGDepAIsTv g) ∨
            Out (frameR p N ∪ {ggDepARefl ha αa}) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro pos c0 m n hpat ha αa hpair hdot hx
  obtain ⟨mi, ni, hmi, hni, rfl, rfl⟩ := twPat1_wit hpat
  have hpatB := (ggTWNPat1B_iff pos c0.val mi ni hmi hni).mpr hpat
  obtain ⟨⟨key, ws, ents⟩, hkey, hchk⟩ := one_of_cover36 hC hS (ggTWPosNat pos) c0.val mi ni
    (twPosNat_mem pos) c0.isLt hmi hni hpatB
  simp only at hkey
  subst hkey
  have hJ : kLo pos ≤ c0.val := kLo_le_of_inJ hpat.1
  rw [twDot_x (N := N) (by omega)] at hx
  obtain ⟨e, d, hed, hde, hfr, hdh, hea, hd0, α', hα', hα0, hα1⟩ := twNorm hpN hN αa hx
  have hex := twE_x (by omega) hde hd0
  have hH := kVec_complete hN pos c0.val ((p - ni % p) % p) (e ha) (Or.inl hJ)
    (twChainH hN pos c0.val _ (e ha) fun c hc => by
      rw [hea, (hpair c hc).2, twCast_neg]
      simp [Fin.ext_iff])
  obtain ⟨u, hu, hA⟩ := kAN_complete hN pos c0.val ((p - mi % p) % p) α' (Or.inl hJ)
    (twChainA hN pos c0.val _ α' fun c hc => by
      rw [hα', hdh, (hpair c hc).1, twCast_neg]
      simp [Fin.ext_iff]) hα0 hα1
  set lh := kVec p N (ggTWPosNat pos) c0.val ((p - ni % p) % p) (vAt (e ha) (kNc N pos)).val
    (vAt (e ha) (kLo pos)).val (vAt (e ha) (N - 1)).val with hlh
  set la := kAN p N (ggTWPosNat pos) c0.val ((p - mi % p) % p) u with hla
  have hd2 : ggDepANDot p la lh = 2 % p :=
    twNDot_eq (kAN_length _ _ _ _) (kVec_length _ _ _ _ _ _) (twMod_lt 2)
      (by rw [hA, hH, hα', twApply_of_mul hde, hdot, twCast_two])
  have hmem : (lh, la) ∈ kCells1 p N (ggTWPosNat pos) c0.val mi ni :=
    mem_kCells1 (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hu hd2
  simp only [kOne] at hchk
  obtain ⟨i, hi⟩ := kAll2_mem _ _ _ hchk _ hmem
  try dsimp only at hi
  have hval : GGTWDValid p N (lh, la) := ⟨kVec_length _ _ _ _ _ _, kAN_length _ _ _ _, hd2⟩
  have hr : d * ggTWDRflOf p N (lh, la) * e = ggDepARefl ha αa := by
    change d * ggDepARefl (ggDepANToZ p N lh) (ggDepANToZ p N la) * e = _
    rw [hH, hA, twRefl_back hde ha αa α' hα']
  refine or_back hOut hed hde hfr hex ?_ ?_ (hE [(lh, la)] ws i ?_ hi)
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [hr]
    exact Set.mem_singleton _
  · intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ⟨(lh, la), List.mem_singleton_self _, hr.symm⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hval

theorem twdk36_cells2 (hp2 : p ≠ 2) (hpN : p ∣ N) (hN : 5 ≤ N) (hE : EntrySound p N F O Out)
    (hOut : OutBack Out) {S : List KOneE} {T : List KTwoE}
    (hF : kFrameOK p N F = true) (hC : kCover36 N S T = true)
    (hT : ∀ i < T.length, kTwoAt p N F O T i = true) :
    ∀ (pos : GGTWPos) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1))),
      GGTWPat2 N pos c.val (c₂.map Fin.val) →
        ∀ ha1 αa1 ha2 αa2 : GGDepAE p N, GGTWDPairs2 p N pos c c₂ ha1 αa1 ha2 αa2 →
          (ggDepAdot αa1 (ggDepAx p N) ≠ 0 ∨ ggDepAdot αa2 (ggDepAx p N) ≠ 0) →
            (∃ g ∈ Submonoid.closure (frameR p N ∪ {ggDepARefl ha1 αa1, ggDepARefl ha2 αa2}),
                GGDepAIsTv g) ∨
              Out (frameR p N ∪ {ggDepARefl ha1 αa1, ggDepARefl ha2 αa2}) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro pos c c₂ hpat ha1 αa1 ha2 αa2 hpair hx
  have hpatB := (ggTWNPat2B_iff pos c.val (c₂.map Fin.val)).mpr hpat
  have hc2m : c₂.map Fin.val ∈ none :: (List.range (N - 1)).map some := by
    cases c₂ with
    | none => exact List.mem_cons_self
    | some d' => exact List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨d'.val, List.mem_range.mpr d'.isLt, rfl⟩)
  obtain ⟨⟨key, ws, ea, eb⟩, hkey, hchk⟩ := two_of_cover36 hC hT (ggTWPosNat pos) c.val
    (c₂.map Fin.val) (twPosNat_mem pos) c.isLt hc2m hpatB
  simp only at hkey
  subst hkey
  simp only [kTwo, Bool.and_eq_true] at hchk
  obtain ⟨hchkA, hchkB⟩ := hchk
  have hJ : kLo pos ≤ c.val := kLo_le_of_inJ hpat.1
  have hJ2 : ∀ c' : Fin (N - 1), c₂ = some c' → kLo pos ≤ c'.val := by
    intro c' hc'
    subst hc'
    exact kLo_le_of_inJ hpat.2.2.1
  obtain ⟨hb, h12, h21, h11, h22⟩ := hpair
  have hp1 : (p - 1) % p < p := twMod_lt _
  set code := ggTWNCode (c₂.map Fin.val) with hcode
  by_cases hx1 : ggDepAdot αa1 (ggDepAx p N) = 0
  ·
    have hx2 : ggDepAdot αa2 (ggDepAx p N) ≠ 0 := hx.resolve_left (not_not.mpr hx1)
    rw [twDot_x (N := N) (by omega)] at hx1 hx2
    obtain ⟨e, d, hed, hde, hfr, hdh, hea, hd0, α', hα', hα0, hα1⟩ := twNorm hpN hN αa2 hx2
    have hex := twE_x (by omega) hde hd0
    have hα1d : ∀ v, ggDepAdot αa1 v = ggDepAdot αa1 (d v) := fun v => (hd0 αa1 hx1 v).symm
    have hH1 := kVec_complete hN pos c.val ((p - 1) % p) (e ha1) (Or.inl hJ)
      (twChainH hN pos c.val _ (e ha1) fun c' hc' => by
        rw [hea, (hb c' hc').2.1, twCast_neg_one]
        simp [Fin.ext_iff])
    have hA1 := kVec_complete hN pos c.val ((p - 1) % p) αa1 (Or.inl hJ)
      (twChainA hN pos c.val _ αa1 fun c' hc' => by
        rw [(hb c' hc').1, twCast_neg_one]
        simp [Fin.ext_iff])
    rw [hx1, ZMod.val_zero] at hA1
    have hH2 := kSolC_complete hN pos c₂ hJ2 (e ha2)
      (chainH2 hN pos c₂ (e ha2) fun c' hc' => by rw [hea, (hb c' hc').2.2.2])
    obtain ⟨u, hu, hA2⟩ := kANC_complete hN pos c₂ hJ2 α'
      (chainA2 hN pos c₂ α' fun c' hc' => by rw [hα', hdh, (hb c' hc').2.2.1]) hα0 hα1
    rw [← hcode] at hH2 hA2
    set lh1 := kVec p N (ggTWPosNat pos) c.val ((p - 1) % p) (vAt (e ha1) (kNc N pos)).val
      (vAt (e ha1) (kLo pos)).val (vAt (e ha1) (N - 1)).val with hlh1
    set la1 := kVec p N (ggTWPosNat pos) c.val ((p - 1) % p) (vAt αa1 (kNc N pos)).val
      (vAt αa1 (kLo pos)).val 0 with hla1
    set lh2 := kSolC p N (ggTWPosNat pos) code (vAt (e ha2) (kNc N pos)).val
      (vAt (e ha2) (kLo pos)).val (vAt (e ha2) (N - 1)).val with hlh2
    set la2 := kANC p N (ggTWPosNat pos) code u with hla2
    have d11 : ggDepANDot p la1 lh1 = 2 % p :=
      twNDot_eq (kVec_length _ _ _ _ _ _) (kVec_length _ _ _ _ _ _) (twMod_lt 2)
        (by rw [hA1, hH1, hα1d, twApply_of_mul hde, h11, twCast_two])
    have d12 : ggDepANDot p la1 lh2 = kBond p code :=
      twNDot_eq (kVec_length _ _ _ _ _ _) (kSolC_length _ _ _ _ _) (kBond_lt _)
        (by rw [hA1, hH2, hα1d, twApply_of_mul hde, h12, hcode, kBond_cast])
    have d22 : ggDepANDot p la2 lh2 = 2 % p :=
      twNDot_eq (kANC_length _ _ _) (kSolC_length _ _ _ _ _) (twMod_lt 2)
        (by rw [hA2, hH2, hα', twApply_of_mul hde, h22, twCast_two])
    have d21 : ggDepANDot p la2 lh1 = kBond p code :=
      twNDot_eq (kANC_length _ _ _) (kVec_length _ _ _ _ _ _) (kBond_lt _)
        (by rw [hA2, hH1, hα', twApply_of_mul hde, h21, hcode, kBond_cast])
    have hmemO : (lh1, la1) ∈ kOuter p N (ggTWPosNat pos) c.val :=
      mem_kOuter (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
        (ZMod.val_lt _) d11
    have hmemI : (lh2, la2) ∈ kInnerC p N (ggTWPosNat pos) code
        (kA2Norm p N (ggTWPosNat pos) code) (lh1, la1) :=
      mem_kInnerC (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) d12 (mem_kA2Norm hu) d22 d21
    refine outer_finish hp2 hN hE hOut hF hed hde hfr hex hchkB hmemO hmemI
      ⟨kVec_length _ _ _ _ _ _, kVec_length _ _ _ _ _ _, d11⟩
      ⟨kSolC_length _ _ _ _ _, kANC_length _ _ _, d22⟩ ?_ ?_
    · change d * ggDepARefl (ggDepANToZ p N lh1) (ggDepANToZ p N la1) * e = _
      rw [hH1, hA1, twRefl_back hde ha1 αa1 αa1 hα1d]
    · change d * ggDepARefl (ggDepANToZ p N lh2) (ggDepANToZ p N la2) * e = _
      rw [hH2, hA2, twRefl_back hde ha2 αa2 α' hα']
  ·
    rw [twDot_x (N := N) (by omega)] at hx1
    obtain ⟨e, d, hed, hde, hfr, hdh, hea, hd0, α', hα', hα0, hα1⟩ := twNorm hpN hN αa1 hx1
    have hex := twE_x (by omega) hde hd0
    obtain ⟨α2', hα2'⟩ := twDual αa2 d
    have hH1 := kVec_complete hN pos c.val ((p - 1) % p) (e ha1) (Or.inl hJ)
      (twChainH hN pos c.val _ (e ha1) fun c' hc' => by
        rw [hea, (hb c' hc').2.1, twCast_neg_one]
        simp [Fin.ext_iff])
    obtain ⟨u, hu, hA1⟩ := kAN_complete hN pos c.val ((p - 1) % p) α' (Or.inl hJ)
      (twChainA hN pos c.val _ α' fun c' hc' => by
        rw [hα', hdh, (hb c' hc').1, twCast_neg_one]
        simp [Fin.ext_iff]) hα0 hα1
    have hH2 := kSolC_complete hN pos c₂ hJ2 (e ha2)
      (chainH2 hN pos c₂ (e ha2) fun c' hc' => by rw [hea, (hb c' hc').2.2.2])
    have hA2 := kSolC_complete hN pos c₂ hJ2 α2'
      (chainA2 hN pos c₂ α2' fun c' hc' => by rw [hα2', hdh, (hb c' hc').2.2.1])
    rw [← hcode] at hH2 hA2
    set lh1 := kVec p N (ggTWPosNat pos) c.val ((p - 1) % p) (vAt (e ha1) (kNc N pos)).val
      (vAt (e ha1) (kLo pos)).val (vAt (e ha1) (N - 1)).val with hlh1
    set la1 := kAN p N (ggTWPosNat pos) c.val ((p - 1) % p) u with hla1
    set lh2 := kSolC p N (ggTWPosNat pos) code (vAt (e ha2) (kNc N pos)).val
      (vAt (e ha2) (kLo pos)).val (vAt (e ha2) (N - 1)).val with hlh2
    set la2 := kSolC p N (ggTWPosNat pos) code (vAt α2' (kNc N pos)).val
      (vAt α2' (kLo pos)).val (vAt α2' (N - 1)).val with hla2
    have d11 : ggDepANDot p la1 lh1 = 2 % p :=
      twNDot_eq (kAN_length _ _ _ _) (kVec_length _ _ _ _ _ _) (twMod_lt 2)
        (by rw [hA1, hH1, hα', twApply_of_mul hde, h11, twCast_two])
    have d12 : ggDepANDot p la1 lh2 = kBond p code :=
      twNDot_eq (kAN_length _ _ _ _) (kSolC_length _ _ _ _ _) (kBond_lt _)
        (by rw [hA1, hH2, hα', twApply_of_mul hde, h12, hcode, kBond_cast])
    have d22 : ggDepANDot p la2 lh2 = 2 % p :=
      twNDot_eq (kSolC_length _ _ _ _ _) (kSolC_length _ _ _ _ _) (twMod_lt 2)
        (by rw [hA2, hH2, hα2', twApply_of_mul hde, h22, twCast_two])
    have d21 : ggDepANDot p la2 lh1 = kBond p code :=
      twNDot_eq (kSolC_length _ _ _ _ _) (kVec_length _ _ _ _ _ _) (kBond_lt _)
        (by rw [hA2, hH1, hα2', twApply_of_mul hde, h21, hcode, kBond_cast])
    have hmemO : (lh1, la1) ∈ kOuterA p N (ggTWPosNat pos) c.val :=
      mem_kOuterA (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hu d11
    have hmemI : (lh2, la2) ∈ kInnerC p N (ggTWPosNat pos) code
        (kA2All p N (ggTWPosNat pos) code) (lh1, la1) :=
      mem_kInnerC (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) d12
        (mem_kA2All (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)) d22 d21
    refine outer_finish hp2 hN hE hOut hF hed hde hfr hex hchkA hmemO hmemI
      ⟨kVec_length _ _ _ _ _ _, kAN_length _ _ _ _, d11⟩
      ⟨kSolC_length _ _ _ _ _, kSolC_length _ _ _ _ _, d22⟩ ?_ ?_
    · change d * ggDepARefl (ggDepANToZ p N lh1) (ggDepANToZ p N la1) * e = _
      rw [hH1, hA1, twRefl_back hde ha1 αa1 α' hα']
    · change d * ggDepARefl (ggDepANToZ p N lh2) (ggDepANToZ p N la2) * e = _
      rw [hH2, hA2, twRefl_back hde ha2 αa2 α2' hα2']

theorem twdk36_or (hp2 : p ≠ 2) (hpN : p ∣ N) (hN : 5 ≤ N) (hE : EntrySound p N F O Out)
    (hOut : OutBack Out) (S : List KOneE) (T : List KTwoE)
    (hF : kFrameOK p N F = true) (hC : kCover36 N S T = true)
    (hS : ∀ i < S.length, kOneAt p N F O S i = true)
    (hT : ∀ i < T.length, kTwoAt p N F O T i = true) : GGTWDCellsOr p N Out :=
  ⟨twdk36_cells1 hp2 hpN hN hE hOut hF hC hS, twdk36_cells2 hp2 hpN hN hE hOut hF hC hT⟩

theorem kTestE_sound36 {F : List GGDepANPair} (O : List KOut) (hF : kFrameOK 3 6 F = true) :
    EntrySound 3 6 F O GGTWDE6Orbit := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro news ws en hnews h
  unfold kTestE at h
  split_ifs at h
  · exact Or.inr (ggTWDOutOK_sound hnews h)
  · exact Or.inl (kTest_sound (by norm_num) (by norm_num) hF hnews _ h)

theorem twdk36_cells (F : List GGDepANPair) (O : List KOut) (S : List KOneE) (T : List KTwoE)
    (hF : kFrameOK 3 6 F = true) (hC : kCover36 6 S T = true)
    (hS : ∀ i < S.length, kOneAt 3 6 F O S i = true)
    (hT : ∀ i < T.length, kTwoAt 3 6 F O T i = true) : GGTWDCells36Orb := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact twdk36_or (by norm_num) (by norm_num) (by norm_num) (kTestE_sound36 O hF) e6_outBack S T
    hF hC hS hT

end CFSG.StandardType.TWDK36

end

module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.RankThree.PartTwo.Sec21.Item23Tools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open Subgroup

section General

variable {A : Type*} [Group A]

private theorem disjoint_of_coprime_of_isPGroup {p : ℕ} {W Q : Subgroup A}
    (hW : Nat.Coprime p (Nat.card W)) (hQ : IsPGroup p Q) : Disjoint W Q := by
  refine Subgroup.disjoint_def.mpr fun {g} hgW hgQ => ?_
  obtain ⟨k, hk⟩ := hQ ⟨g, hgQ⟩
  have h1 : orderOf g ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hW.pow_left k).symm (Subgroup.orderOf_dvd_natCard W hgW) h1)

private theorem comm_mem_left {W : Subgroup A} {w x : A} (hw : w ∈ W)
    (hx : x ∈ normalizer (W : Set A)) : w * x * w⁻¹ * x⁻¹ ∈ W := by
  have h : x * w⁻¹ * x⁻¹ ∈ W := (mem_normalizer_iff.mp hx _).mp (W.inv_mem hw)
  have e : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
  rw [e]
  exact W.mul_mem hw h

private theorem comm_mem_right {Q : Subgroup A} {w x : A} (hx : x ∈ Q)
    (hw : w ∈ normalizer (Q : Set A)) : w * x * w⁻¹ * x⁻¹ ∈ Q :=
  Q.mul_mem ((mem_normalizer_iff.mp hw x).mp hx) (Q.inv_mem hx)

private theorem mul_comm_of_comm_eq_one {w x : A} (h : w * x * w⁻¹ * x⁻¹ = 1) :
    x * w = w * x := by
  have e : w * x = (w * x * w⁻¹ * x⁻¹) * (x * w) := by group
  rw [h, one_mul] at e
  exact e.symm

theorem eq_bot_of_normalizer_of_centralizer_le {p : ℕ} {K Q W : Subgroup A} [hK : K.Normal]
    (hQ : IsPGroup p Q) (hW : Nat.Coprime p (Nat.card W)) (hQK : Q ≤ K)
    (hQW : Q ≤ normalizer (W : Set A)) (hWQ : W ⊓ K ≤ normalizer (Q : Set A))
    (hCQ : W ⊓ centralizer (Q : Set A) ≤ Q) : W = ⊥ := by
  have hdisj := disjoint_of_coprime_of_isPGroup hW hQ
  have hWK : W ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hwC : w ∈ centralizer (Q : Set A) := by
      rw [mem_centralizer_iff]
      intro x hx
      exact mul_comm_of_comm_eq_one (Subgroup.disjoint_def.mp hdisj
        (comm_mem_left hw.1 (hQW hx)) (comm_mem_right hx (hWQ hw)))
    exact mem_bot.mpr (Subgroup.disjoint_def.mp hdisj hw.1 (hCQ ⟨hw.1, hwC⟩))
  rw [eq_bot_iff]
  intro w hw
  have hwC : w ∈ centralizer (Q : Set A) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hc : w * x * w⁻¹ * x⁻¹ ∈ W ⊓ K :=
      ⟨comm_mem_left hw (hQW hx), K.mul_mem (hK.conj_mem x (hQK hx) w) (K.inv_mem (hQK hx))⟩
    rw [hWK, mem_bot] at hc
    exact mul_comm_of_comm_eq_one hc
  exact mem_bot.mpr (Subgroup.disjoint_def.mp hdisj hw (hCQ ⟨hw, hwC⟩))

theorem eq_bot_of_plane [Finite A] {p : ℕ} (hp : p.Prime) {B V : Subgroup A}
    (hBexp : ∀ b ∈ B, b ^ p = 1) (hBcard : Nat.card B = p ^ 2)
    (hV : Nat.Coprime p (Nat.card V)) (hBV : B ≤ normalizer (V : Set A))
    (h : ∀ b ∈ B, b ≠ 1 → V ⊓ centralizer ({b} : Set A) = ⊥) : V = ⊥ := by
  refine (CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p hp
    B V (fun b => Subtype.ext (by simpa using hBexp b b.2)) hBcard (hp.coprime_iff_not_dvd.mp hV)
    hBV).trans ?_
  exact iSup_eq_bot.mpr fun b => iSup_eq_bot.mpr fun hb =>
    h b b.2 fun h1 => hb (Subtype.ext h1)

theorem eq_bot_of_sig [Finite A] {p : ℕ} (hp : p.Prime) {K B Q V : Subgroup A} [K.Normal]
    (hBexp : ∀ b ∈ B, b ^ p = 1) (hBcard : Nat.card B = p ^ 2) (hQ : IsPGroup p Q)
    (hQK : Q ≤ K) (hQB : Q ≤ centralizer (B : Set A))
    (hCb : ∀ b ∈ B, b ≠ 1 → K ⊓ centralizer ({b} : Set A) ≤ normalizer (Q : Set A))
    (hCQ : centralizer (Q : Set A) ≤ Q) (hV : Nat.Coprime p (Nat.card V))
    (hBV : B ≤ normalizer (V : Set A)) (hQV : Q ≤ normalizer (V : Set A)) : V = ⊥ := by
  refine eq_bot_of_plane hp hBexp hBcard hV hBV fun b hb hb1 => ?_
  have hQb : Q ≤ centralizer ({b} : Set A) :=
    hQB.trans (centralizer_le (Set.singleton_subset_iff.mpr hb))
  refine eq_bot_of_normalizer_of_centralizer_le (K := K) hQ
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hV) hQK ?_ ?_ ?_
  · exact (le_inf hQV (hQb.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  · exact fun w hw => hCb b hb hb1 ⟨hw.2, hw.1.2⟩
  · exact fun w hw => hCQ hw.2

theorem le_normal_of_inf_centralizer_eq_bot {K E : Subgroup A} [hK : K.Normal] [Finite E] {z : A}
    (hzK : z ∈ K) (hzE : z ∈ normalizer (E : Set A))
    (hE : E ⊓ centralizer ({z} : Set A) = ⊥) : E ≤ K := by
  let f : E → E := fun e =>
    ⟨(e : A)⁻¹ * (z * e * z⁻¹), E.mul_mem (E.inv_mem e.2) ((mem_normalizer_iff.mp hzE e).mp e.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h : (a : A)⁻¹ * (z * a * z⁻¹) = (b : A)⁻¹ * (z * b * z⁻¹) := congrArg Subtype.val hab
    have h' : (a : A)⁻¹ * z * a = (b : A)⁻¹ * z * b := by
      calc (a : A)⁻¹ * z * a = (a : A)⁻¹ * (z * a * z⁻¹) * z := by group
        _ = (b : A)⁻¹ * (z * b * z⁻¹) * z := by rw [h]
        _ = (b : A)⁻¹ * z * b := by group
    have hmem : (b : A) * (a : A)⁻¹ ∈ E ⊓ centralizer ({z} : Set A) := by
      refine ⟨E.mul_mem b.2 (E.inv_mem a.2), mem_centralizer_singleton_iff.mpr ?_⟩
      calc (b : A) * (a : A)⁻¹ * z = b * ((a : A)⁻¹ * z * a) * (a : A)⁻¹ := by group
        _ = b * ((b : A)⁻¹ * z * b) * (a : A)⁻¹ := by rw [h']
        _ = z * ((b : A) * (a : A)⁻¹) := by group
    rw [hE, mem_bot, mul_inv_eq_one] at hmem
    exact Subtype.ext hmem.symm
  intro x hx
  obtain ⟨e, he⟩ := Finite.surjective_of_injective hf ⟨x, hx⟩
  have hx' : x = (e : A)⁻¹ * z * e * z⁻¹ := by
    have h := congrArg Subtype.val he
    change (e : A)⁻¹ * (z * e * z⁻¹) = x at h
    rw [← h]
    group
  rw [hx']
  have h1 : (e : A)⁻¹ * z * e ∈ K := by simpa using hK.conj_mem z hzK (e : A)⁻¹
  exact K.mul_mem h1 (K.inv_mem hzK)

private theorem isElemAbelian_of_le {q : ℕ} {E F : Subgroup A} (hF : IsElemAbelian q F)
    (hEF : E ≤ F) : IsElemAbelian q E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hF.2 x (hEF hx)⟩
  exact (congrArg Subtype.val (hF.1.is_comm.comm (⟨a, hEF a.2⟩ : F) ⟨b, hEF b.2⟩) :)

private theorem isPGroup_of_isElemAbelian {q : ℕ} {E : Subgroup A} (hE : IsElemAbelian q E) :
    IsPGroup q E :=
  fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩

theorem coprime_card_of_isPGroup [Finite A] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {V : Subgroup A} (hV : IsPGroup q V) : Nat.Coprime p (Nat.card V) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  rw [hk]
  exact ((Nat.coprime_primes hp hq).mpr hpq).pow_right k

theorem forall_eq_bot_of_selfCentralizing [Finite A] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {K T Q : Subgroup A} [K.Normal] {z : A} (hQ : IsPGroup p Q) (hQK : Q ≤ K)
    (hQT : Q ≤ T) (hzQ : K ⊓ centralizer ({z} : Set A) ≤ normalizer (Q : Set A))
    (hCQ : centralizer ({z} : Set A) ⊓ centralizer (Q : Set A) ≤ Q) :
    ∀ W : Subgroup A, IsElemAbelian q W → W ≤ centralizer ({z} : Set A) →
      T ≤ normalizer (W : Set A) → W = ⊥ := by
  intro W hW hWz hTW
  exact eq_bot_of_normalizer_of_centralizer_le (K := K) hQ
    (coprime_card_of_isPGroup hp hq hpq (isPGroup_of_isElemAbelian hW)) hQK (hQT.trans hTW)
    (fun w hw => hzQ ⟨hw.2, hWz hw.1⟩) (fun w hw => hCQ ⟨hWz hw.1, hw.2⟩)

end General

section Central

variable {A : Type} [Group A]

open CFSG.RankThree.PartTwo.Sec21 in
theorem eq_bot_of_central [Finite A] {q : ℕ} (hq : q.Prime) {K T V : Subgroup A} [K.Normal]
    {z : A} (hzK : z ∈ K) (hzV : z ∈ normalizer (V : Set A))
    (hTz : T ≤ centralizer ({z} : Set A))
    (h1 : ∀ W : Subgroup A, IsElemAbelian q W → W ≤ centralizer ({z} : Set A) →
      T ≤ normalizer (W : Set A) → W = ⊥)
    (h2 : ∀ E : Subgroup A, IsElemAbelian q E → E ≤ K → T ≤ normalizer (E : Set A) →
      E ⊓ centralizer ({z} : Set A) = ⊥ → E = ⊥)
    (hV : IsPGroup q V) (hTV : T ≤ normalizer (V : Set A)) : V = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hV1
  set E := omegaOneCenterOf q V
  have hE : IsElemAbelian q E := isElemAbelian_omegaOneCenterOf q V
  have hE1 : E ≠ ⊥ := omegaOneCenterOf_ne_bot hV hV1
  have hTE : T ≤ normalizer (E : Set A) :=
    hTV.trans (normalizer_le_normalizer_omegaOneCenterOf q V)
  by_cases hC : E ⊓ centralizer ({z} : Set A) = ⊥
  · exact hE1 (h2 E hE (le_normal_of_inf_centralizer_eq_bot hzK
      (normalizer_le_normalizer_omegaOneCenterOf q V hzV) hC) hTE hC)
  · exact hC (h1 _ (isElemAbelian_of_le hE inf_le_left) inf_le_right
      ((le_inf hTE (hTz.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf))

end Central

section MulAut

private theorem conj_injective {K : Type*} [Group K] (hZ : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxZ : x ∈ center K := by
    rw [mem_center_iff]
    intro g
    have h := congrArg (fun f : MulAut K => f g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * x = (x * g * x⁻¹) * x := by rw [h]
      _ = x * g := by group
  rw [hZ, mem_bot] at hxZ
  exact hxZ

private theorem normal_range_conj {K : Type*} [Group K] :
    ((MulAut.conj : K →* MulAut K).range).Normal := by
  refine ⟨fun n hn f => ?_⟩
  obtain ⟨x, rfl⟩ := hn
  refine ⟨f x, ?_⟩
  ext y
  simp [MulAut.conj_apply]

private theorem conj_mem_normalizer_map {K : Type*} [Group K] {Q : Subgroup K} {x : K}
    (hx : x ∈ normalizer (Q : Set K)) :
    MulAut.conj x ∈ normalizer ((Q.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K)) :=
  le_normalizer_map (MulAut.conj : K →* MulAut K) ⟨x, hx, rfl⟩

theorem mulAut_eq_bot_of_sig {K : Type*} [Group K] [Finite K] (hZ : center K = ⊥) {p : ℕ}
    (hp : p.Prime) {T B Q : Subgroup K} (hBT : B ≤ T) (hQT : Q ≤ T)
    (hBexp : ∀ b ∈ B, b ^ p = 1) (hBcard : Nat.card B = p ^ 2) (hQ : IsPGroup p Q)
    (hQB : Q ≤ centralizer (B : Set K))
    (hCb : ∀ b ∈ B, b ≠ 1 → centralizer ({b} : Set K) ≤ normalizer (Q : Set K))
    (hCQ : centralizer ((Q.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K)) ≤ Q.map (MulAut.conj : K →* MulAut K))
    (V : Subgroup (MulAut K)) (hV : Nat.Coprime p (Nat.card V))
    (hTV : ∀ t ∈ T, MulAut.conj t ∈ normalizer (V : Set (MulAut K))) : V = ⊥ := by
  haveI := normal_range_conj (K := K)
  have hinj := conj_injective hZ
  refine eq_bot_of_sig (K := (MulAut.conj : K →* MulAut K).range)
    (B := B.map (MulAut.conj : K →* MulAut K)) hp ?_ ?_ (hQ.map _) (map_le_range _ _) ?_ ?_ hCQ
    hV ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hBexp b hb, map_one]
  · rw [card_map_of_injective hinj, hBcard]
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (hQB hx) b hb]
  · rintro _ ⟨b, hb, rfl⟩ hb1 _ ⟨⟨k, rfl⟩, hk⟩
    have hb1' : b ≠ 1 := by
      rintro rfl
      exact hb1 (map_one _)
    refine conj_mem_normalizer_map (hCb b hb hb1' (mem_centralizer_singleton_iff.mpr ?_))
    exact hinj (by rw [map_mul, map_mul]; exact mem_centralizer_singleton_iff.mp hk)
  · rintro _ ⟨b, hb, rfl⟩
    exact hTV b (hBT hb)
  · rintro _ ⟨x, hx, rfl⟩
    exact hTV x (hQT hx)

theorem mulAut_forall_eq_bot_of_selfCentralizing {K : Type*} [Group K] [Finite K]
    (hZ : center K = ⊥) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {T Q : Subgroup K} {z : K} (hQ : IsPGroup p Q) (hQT : Q ≤ T)
    (hzQ : centralizer ({z} : Set K) ≤ normalizer (Q : Set K))
    (hCQ : centralizer ({MulAut.conj z} : Set (MulAut K)) ⊓
      centralizer ((Q.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K)) ≤ Q.map (MulAut.conj : K →* MulAut K)) :
    ∀ W : Subgroup (MulAut K), IsElemAbelian q W →
      W ≤ centralizer ({MulAut.conj z} : Set (MulAut K)) →
      (∀ t ∈ T, MulAut.conj t ∈ normalizer (W : Set (MulAut K))) → W = ⊥ := by
  haveI := normal_range_conj (K := K)
  have hinj := conj_injective hZ
  intro W hW hWz hTW
  refine forall_eq_bot_of_selfCentralizing (K := (MulAut.conj : K →* MulAut K).range)
    (T := T.map (MulAut.conj : K →* MulAut K)) hp hq hpq (hQ.map _) (map_le_range _ _)
    (map_mono hQT) ?_ hCQ W hW hWz ?_
  · rintro _ ⟨⟨k, rfl⟩, hk⟩
    refine conj_mem_normalizer_map (hzQ (mem_centralizer_singleton_iff.mpr ?_))
    exact hinj (by rw [map_mul, map_mul]; exact mem_centralizer_singleton_iff.mp hk)
  · rintro _ ⟨t, ht, rfl⟩
    exact hTW t ht

theorem mulAut_eq_bot_of_central {K : Type} [Group K] [Finite K] (hZ : center K = ⊥) {q : ℕ}
    (hq : q.Prime) {T : Subgroup K} {z : K} (hzT : z ∈ T) (hTz : T ≤ centralizer ({z} : Set K))
    (h1 : ∀ W : Subgroup (MulAut K), IsElemAbelian q W →
      W ≤ centralizer ({MulAut.conj z} : Set (MulAut K)) →
      (∀ t ∈ T, MulAut.conj t ∈ normalizer (W : Set (MulAut K))) → W = ⊥)
    (h2 : ∀ E : Subgroup K, IsElemAbelian q E → T ≤ normalizer (E : Set K) →
      E ⊓ centralizer ({z} : Set K) = ⊥ → E = ⊥)
    (V : Subgroup (MulAut K)) (hV : IsPGroup q V)
    (hTV : ∀ t ∈ T, MulAut.conj t ∈ normalizer (V : Set (MulAut K))) : V = ⊥ := by
  haveI := normal_range_conj (K := K)
  have hinj := conj_injective hZ
  set ι : K →* MulAut K := MulAut.conj
  refine eq_bot_of_central (K := ι.range) (T := T.map ι) hq ⟨z, rfl⟩ (hTV z hzT) ?_
    (fun W hW hWz hTW => h1 W hW hWz fun t ht => hTW ⟨t, ht, rfl⟩) ?_ hV
    (fun _ ⟨t, ht, e⟩ => e ▸ hTV t ht)
  · rintro _ ⟨t, ht, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (hTz ht)]
  · intro E hE hEK hTE hEz
    set E₀ := E.comap ι
    have hmap : E₀.map ι = E := map_comap_eq_self hEK
    have hE₀ab : IsElemAbelian q E₀ := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
      · change ι (a * b) = ι (b * a)
        rw [map_mul, map_mul]
        exact congrArg Subtype.val (hE.1.is_comm.comm (⟨ι a, a.2⟩ : E) ⟨ι b, b.2⟩)
      · rw [map_pow, map_one]
        exact hE.2 _ hx
    have hTE₀ : T ≤ normalizer (E₀ : Set K) := by
      rw [le_normalizer_iff]
      intro t ht x hx
      change ι (t * x * t⁻¹) ∈ E
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp (hTE ⟨t, ht, rfl⟩) _).mp hx
    have hE₀z : E₀ ⊓ centralizer ({z} : Set K) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx, hxz⟩
      have hmem : ι x ∈ E ⊓ centralizer ({ι z} : Set (MulAut K)) := by
        refine ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hxz]
      rw [hEz, mem_bot] at hmem
      exact mem_bot.mpr (hinj (hmem.trans (map_one ι).symm))
    rw [← hmap, h2 E₀ hE₀ab hTE₀ hE₀z, Subgroup.map_bot]

end MulAut

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

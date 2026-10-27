module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace ChiefOfA5

variable {G : Type} [Group G]

private theorem conj_mem_of_normalizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {h : G} (hh : h ∈ H) : g * h * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg h).mp hh

private theorem le_normalizer_of_conj {P H : Subgroup G}
    (h : ∀ p ∈ P, ∀ y ∈ H, p * y * p⁻¹ ∈ H) : P ≤ Subgroup.normalizer (H : Set G) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => h p hp g hg, fun hg => ?_⟩
  have e : p⁻¹ * (p * g * p⁻¹) * p⁻¹⁻¹ = g := by group
  have := h p⁻¹ (P.inv_mem hp) _ hg
  rwa [e] at this

private theorem comm_mem_of {H : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    ⁅x, y⁆ ∈ H := by
  simp only [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

private theorem relIndex_pos_of_le [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    0 < H.relIndex K := by
  have h1 := Subgroup.relIndex_dvd_index_of_le h
  have h2 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine Nat.pos_of_ne_zero fun h0 => h2 ?_
  rw [h0, zero_dvd_iff] at h1
  exact h1

private theorem hall_witt_conj {P K : Subgroup G} (hPK : P ≤ Subgroup.normalizer (K : Set G))
    {a b c x y z : G} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hy : y ∈ K) (hz : z ∈ K)
    (h : a * x * a⁻¹ * c * y * c⁻¹ * b * z * b⁻¹ = 1) : x ∈ K := by
  have hu : c * y * c⁻¹ ∈ K := conj_mem_of_normalizer (hPK hc) hy
  have hv : b * z * b⁻¹ ∈ K := conj_mem_of_normalizer (hPK hb) hz
  have h1 : a * x * a⁻¹ * (c * y * c⁻¹ * (b * z * b⁻¹)) = 1 := by
    calc a * x * a⁻¹ * (c * y * c⁻¹ * (b * z * b⁻¹))
        = a * x * a⁻¹ * c * y * c⁻¹ * b * z * b⁻¹ := by group
      _ = 1 := h
  have h2 : a * x * a⁻¹ ∈ K := by
    have e : a * x * a⁻¹ = (c * y * c⁻¹ * (b * z * b⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [e]
    exact K.inv_mem (K.mul_mem hu hv)
  have h3 := conj_mem_of_normalizer (hPK (P.inv_mem ha)) h2
  have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
  rwa [e] at h3

private theorem two_step {P L X T K : Subgroup G} (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hLP : L ≤ P) (hXP : X ≤ P) (hperf : ⁅L, L⁆ = L) (hT : ∀ t ∈ T, ∀ l ∈ L, ⁅t, l⁆ ∈ K)
    (hXT : ∀ l ∈ L, ∀ x ∈ X, ⁅l, x⁆ ∈ T) : ∀ c ∈ X, ∀ y ∈ L, ⁅y, c⁆ ∈ K := by
  have hK : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K :=
    fun g hg k hk => conj_mem_of_normalizer (hPK hg) hk
  have hHW : ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ X, ⁅⁅a⁻¹, b⁆, c⁆ ∈ K := by
    intro a ha b hb c hc
    have hw : ⁅c⁻¹, a⁆ ∈ T := by
      rw [← commutatorElement_inv]
      exact T.inv_mem (hXT a ha c⁻¹ (X.inv_mem hc))
    have hY : ⁅⁅c⁻¹, a⁆, b⁆ ∈ K := hT _ hw b hb
    have hZ : ⁅⁅b⁻¹, c⁆, a⁆ ∈ K := hT _ (hXT b⁻¹ (L.inv_mem hb) c hc) a ha
    exact hall_witt_conj hPK (hLP ha) (hLP hb) (hXP hc) hY hZ
      (conj_commutatorElement_left_commutatorElement_mul a b c)
  intro c hc
  let D : Subgroup G :=
    { carrier := {y | y ∈ L ∧ ⁅y, c⁆ ∈ K}
      mul_mem' := by
        rintro y z ⟨hy, hyc⟩ ⟨hz, hzc⟩
        refine ⟨L.mul_mem hy hz, ?_⟩
        have e : ⁅y * z, c⁆ = y * ⁅z, c⁆ * y⁻¹ * ⁅y, c⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact K.mul_mem (hK y (hLP hy) _ hzc) hyc
      one_mem' := by
        refine ⟨L.one_mem, ?_⟩
        rw [commutatorElement_one_left]
        exact K.one_mem
      inv_mem' := by
        rintro y ⟨hy, hyc⟩
        refine ⟨L.inv_mem hy, ?_⟩
        have e : ⁅y⁻¹, c⁆ = y⁻¹ * ⁅y, c⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hK y⁻¹ (P.inv_mem (hLP hy)) _ (K.inv_mem hyc) }
  have hLD : ⁅L, L⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h := hHW g₁⁻¹ (L.inv_mem hg₁) g₂ hg₂ c hc
    rw [inv_inv] at h
    exact ⟨comm_mem_of hg₁ hg₂, h⟩
  intro y hy
  have hy' : y ∈ ⁅L, L⁆ := by rw [hperf]; exact hy
  exact (show y ∈ L ∧ ⁅y, c⁆ ∈ K from hLD hy').2

private theorem exists_fixed_mod [Finite G] {P X T : Subgroup G} (hXP : X ≤ P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hTX : T < X) (hsq : ∀ x ∈ X, x ^ 2 ∈ T) :
    ∃ x ∈ X, x ∉ T ∧ ∀ q ∈ pCoreOf 2 P, ⁅q, x⁆ ∈ T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hQP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  haveI hN : (T.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := conj_mem_of_normalizer (hPT (hXP g.2)) hn
    simpa using h⟩
  let φ : ↥(pCoreOf 2 P) → (↥X →* ↥X) := fun q =>
    { toFun := fun x => ⟨(q : G) * x * (q : G)⁻¹, conj_mem_of_normalizer (hPX (hQP q.2)) x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hφN : ∀ q : ↥(pCoreOf 2 P), T.subgroupOf X ≤ (T.subgroupOf X).comap (φ q) := by
    intro q n hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hn
    show (q : G) * (n : G) * (q : G)⁻¹ ∈ T
    exact conj_mem_of_normalizer (hPT (hQP q.2)) hn
  letI act : MulAction ↥(pCoreOf 2 P) (X ⧸ T.subgroupOf X) :=
    { smul := fun q z => QuotientGroup.map (T.subgroupOf X) (T.subgroupOf X) (φ q) (hφN q) z
      one_smul := by
        intro z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
        show QuotientGroup.map (T.subgroupOf X) (T.subgroupOf X) (φ 1) (hφN 1) x = x
        rw [QuotientGroup.map_mk]
        congr 1
        exact Subtype.ext (by simp [φ])
      mul_smul := by
        intro q r z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
        show QuotientGroup.map (T.subgroupOf X) (T.subgroupOf X) (φ (q * r)) (hφN (q * r)) x =
          QuotientGroup.map (T.subgroupOf X) (T.subgroupOf X) (φ q) (hφN q)
            (QuotientGroup.map (T.subgroupOf X) (T.subgroupOf X) (φ r) (hφN r) x)
        rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.map_mk]
        congr 1
        exact Subtype.ext (by simp [φ, mul_assoc]) }
  have one_fix : (1 : X ⧸ T.subgroupOf X) ∈
      MulAction.fixedPoints ↥(pCoreOf 2 P) (X ⧸ T.subgroupOf X) := by
    rw [MulAction.mem_fixedPoints]
    intro q
    show QuotientGroup.map (T.subgroupOf X) (T.subgroupOf X) (φ q) (hφN q) 1 = 1
    exact map_one _
  obtain ⟨x0, hx0X, hx0T⟩ := SetLike.exists_of_lt hTX
  set u : X ⧸ T.subgroupOf X := QuotientGroup.mk ⟨x0, hx0X⟩ with hu_def
  have hu1 : u ≠ 1 := by
    intro h
    rw [hu_def, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hx0T h
  have hu2 : u ^ 2 = 1 := by
    rw [hu_def, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hsq x0 hx0X
  have h2dvd : 2 ∣ Nat.card (X ⧸ T.subgroupOf X) := by
    have h := orderOf_dvd_natCard u
    rwa [orderOf_eq_prime hu2 hu1] at h
  have hmod := hQ2.card_modEq_card_fixedPoints (X ⧸ T.subgroupOf X)
  have hF2 : 2 ∣ Nat.card (MulAction.fixedPoints ↥(pCoreOf 2 P) (X ⧸ T.subgroupOf X)) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h2dvd))
  obtain ⟨z, hzF, hz1⟩ :
      ∃ z ∈ MulAction.fixedPoints ↥(pCoreOf 2 P) (X ⧸ T.subgroupOf X), z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton
        (MulAction.fixedPoints ↥(pCoreOf 2 P) (X ⧸ T.subgroupOf X)) :=
      ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
    have hle := Finite.card_le_one_iff_subsingleton.mpr hsub
    haveI : Nonempty (MulAction.fixedPoints ↥(pCoreOf 2 P) (X ⧸ T.subgroupOf X)) :=
      ⟨⟨1, one_fix⟩⟩
    have hpos := Nat.card_pos (α := MulAction.fixedPoints ↥(pCoreOf 2 P) (X ⧸ T.subgroupOf X))
    omega
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨(x : G), x.2, fun hxT => hz1 ?_, fun q hq => ?_⟩
  · exact (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hxT)
  · have hfix : ((φ ⟨q, hq⟩ x : X) : X ⧸ T.subgroupOf X) = (x : X ⧸ T.subgroupOf X) :=
      MulAction.mem_fixedPoints.mp hzF ⟨q, hq⟩
    have h1 : (φ ⟨q, hq⟩ x)⁻¹ * x ∈ T.subgroupOf X := QuotientGroup.eq.mp hfix
    rw [Subgroup.mem_subgroupOf] at h1
    have h1' : ((q : G) * (x : G) * (q : G)⁻¹)⁻¹ * (x : G) ∈ T := by
      simpa [φ] using h1
    have h3 := conj_mem_of_normalizer (hPT (hXP x.2)) h1'
    have e : (x : G) * (((q : G) * (x : G) * (q : G)⁻¹)⁻¹ * (x : G)) * (x : G)⁻¹ =
        ⁅(q : G), (x : G)⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e] at h3
    exact T.inv_mem_iff.mp h3

end ChiefOfA5

theorem leafChiefOfA5 [DSLeaf LeafFaithfulA5] : LeafChiefOfA5 := by
  intro G _ _ P L E K hLP hPL hEP hPE hPK hsec hcard hq hperf hnt
  classical
  obtain ⟨hKE, hEEK, hsqK⟩ : K ≤ E ∧ ⁅E, E⁆ ≤ K ∧ ∀ e ∈ E, e ^ 2 ∈ K := hsec
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hKP : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K :=
    fun g hg k hk => ChiefOfA5.conj_mem_of_normalizer (hPK hg) hk
  have hLL : ⁅L, L⁆ = L := (perfectCore_eq_self_iff L).mp hperf
  have hQP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hQN : ∀ p ∈ P, ∀ q ∈ pCoreOf 2 P, p * q * p⁻¹ ∈ pCoreOf 2 P := fun p hp q hq =>
    ChiefOfA5.conj_mem_of_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hp) hq
  obtain ⟨T, hTmem⟩ : ∃ T : Subgroup G, ∀ g, g ∈ T ↔ g ∈ E ∧ ∀ l ∈ L, ⁅g, l⁆ ∈ K := by
    refine ⟨{ carrier := {g | g ∈ E ∧ ∀ l ∈ L, ⁅g, l⁆ ∈ K}
              one_mem' := ⟨E.one_mem, fun l _ => by
                rw [commutatorElement_one_left]; exact K.one_mem⟩
              mul_mem' := ?_
              inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · rintro g h ⟨hg, hgl⟩ ⟨hh, hhl⟩
      refine ⟨E.mul_mem hg hh, fun l hl => ?_⟩
      have e : ⁅g * h, l⁆ = g * ⁅h, l⁆ * g⁻¹ * ⁅g, l⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact K.mul_mem (hKP g (hEP hg) _ (hhl l hl)) (hgl l hl)
    · rintro g ⟨hg, hgl⟩
      refine ⟨E.inv_mem hg, fun l hl => ?_⟩
      have e : ⁅g⁻¹, l⁆ = g⁻¹ * ⁅g, l⁆⁻¹ * g⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hKP g⁻¹ (P.inv_mem (hEP hg)) _ (K.inv_mem (hgl l hl))
  have hKT : K ≤ T := by
    intro k hk
    refine (hTmem k).mpr ⟨hKE hk, fun l hl => ?_⟩
    have e : ⁅k, l⁆ = k * (l * k⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem hk (hKP l (hLP hl) _ (K.inv_mem hk))
  have hTE : T ≤ E := fun t ht => ((hTmem t).mp ht).1
  have hTP : ∀ p ∈ P, ∀ t ∈ T, p * t * p⁻¹ ∈ T := by
    intro p hp t ht
    obtain ⟨htE, htL⟩ := (hTmem t).mp ht
    refine (hTmem _).mpr ⟨ChiefOfA5.conj_mem_of_normalizer (hPE hp) htE, fun l hl => ?_⟩
    have hl' : p⁻¹ * l * p⁻¹⁻¹ ∈ L := ChiefOfA5.conj_mem_of_normalizer (hPL (P.inv_mem hp)) hl
    have e : ⁅p * t * p⁻¹, l⁆ = p * ⁅t, p⁻¹ * l * p⁻¹⁻¹⁆ * p⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hKP p hp _ (htL _ hl')
  have hPTn : P ≤ Subgroup.normalizer (T : Set G) := ChiefOfA5.le_normalizer_of_conj hTP
  have hTE' : T < E := by
    refine lt_of_le_of_ne hTE fun h => ?_
    obtain ⟨l0, hl0, e0, he0, hne0⟩ := hnt
    have he0T : e0 ∈ T := by rw [h]; exact he0
    apply hne0
    rw [← commutatorElement_inv]
    exact K.inv_mem (((hTmem e0).mp he0T).2 l0 hl0)
  obtain ⟨X, ⟨hTX, hXE, hPX⟩, hXmin⟩ := WellFounded.has_min wellFounded_lt
    {Y : Subgroup G | T < Y ∧ Y ≤ E ∧ P ≤ Subgroup.normalizer (Y : Set G)}
    ⟨E, hTE', le_rfl, hPE⟩
  have hXP : X ≤ P := hXE.trans hEP
  have hnt' : ∃ l ∈ L, ∃ x ∈ X, ⁅l, x⁆ ∉ T := by
    by_contra hcon
    push Not at hcon
    have hc := ChiefOfA5.two_step hPK hLP hXP hLL
      (fun t ht l hl => ((hTmem t).mp ht).2 l hl) hcon
    apply (show T ≤ X ∧ ¬ X ≤ T from hTX).2
    intro c hc'
    refine (hTmem c).mpr ⟨hXE hc', fun l hl => ?_⟩
    rw [← commutatorElement_inv]
    exact K.inv_mem (hc c hc' l hl)
  have hsq : ∀ x ∈ X, x ^ 2 ∈ T := fun x hx => hKT (hsqK x (hXE hx))
  have hcore : ∀ q ∈ pCoreOf 2 P, ∀ e ∈ X, ⁅q, e⁆ ∈ T := by
    obtain ⟨x, hxX, hxT, hfix⟩ := ChiefOfA5.exists_fixed_mod hXP hPX hPTn hTX hsq
    let F : Subgroup G :=
      { carrier := {y | y ∈ X ∧ ∀ q ∈ pCoreOf 2 P, ⁅q, y⁆ ∈ T}
        mul_mem' := by
          rintro y z ⟨hy, hyq⟩ ⟨hz, hzq⟩
          refine ⟨X.mul_mem hy hz, fun q hq => ?_⟩
          have e : ⁅q, y * z⁆ = ⁅q, y⁆ * (y * ⁅q, z⁆ * y⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact T.mul_mem (hyq q hq)
            (ChiefOfA5.conj_mem_of_normalizer (hPTn (hXP hy)) (hzq q hq))
        one_mem' := by
          refine ⟨X.one_mem, fun q _ => ?_⟩
          rw [commutatorElement_one_right]
          exact T.one_mem
        inv_mem' := by
          rintro y ⟨hy, hyq⟩
          refine ⟨X.inv_mem hy, fun q hq => ?_⟩
          have e : ⁅q, y⁻¹⁆ = y⁻¹ * ⁅q, y⁆⁻¹ * y⁻¹⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact ChiefOfA5.conj_mem_of_normalizer (hPTn (hXP (X.inv_mem hy)))
            (T.inv_mem (hyq q hq)) }
    have hF_sub : F ≤ X := fun y hy => (show y ∈ X ∧ _ from hy).1
    have hTF : T ≤ F := by
      intro t ht
      refine (show t ∈ X ∧ ∀ q ∈ pCoreOf 2 P, ⁅q, t⁆ ∈ T from ⟨hTX.le ht, fun q hq => ?_⟩)
      have e : ⁅q, t⁆ = (q * t * q⁻¹) * t⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact T.mul_mem (ChiefOfA5.conj_mem_of_normalizer (hPTn (hQP hq)) ht) (T.inv_mem ht)
    have hFP : ∀ p ∈ P, ∀ y ∈ F, p * y * p⁻¹ ∈ F := by
      intro p hp y hy
      obtain ⟨hyX, hyq⟩ := (show y ∈ X ∧ ∀ q ∈ pCoreOf 2 P, ⁅q, y⁆ ∈ T from hy)
      refine (show p * y * p⁻¹ ∈ X ∧ ∀ q ∈ pCoreOf 2 P, ⁅q, p * y * p⁻¹⁆ ∈ T from
        ⟨ChiefOfA5.conj_mem_of_normalizer (hPX hp) hyX, fun q hq => ?_⟩)
      have hq' : p⁻¹ * q * p⁻¹⁻¹ ∈ pCoreOf 2 P := hQN p⁻¹ (P.inv_mem hp) q hq
      have e : ⁅q, p * y * p⁻¹⁆ = p * ⁅p⁻¹ * q * p⁻¹⁻¹, y⁆ * p⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact ChiefOfA5.conj_mem_of_normalizer (hPTn hp) (hyq _ hq')
    have hFPn : P ≤ Subgroup.normalizer (F : Set G) := ChiefOfA5.le_normalizer_of_conj hFP
    have hTltF : T < F := by
      refine lt_of_le_of_ne hTF fun h => ?_
      apply hxT
      rw [h]
      exact (show x ∈ X ∧ ∀ q ∈ pCoreOf 2 P, ⁅q, x⁆ ∈ T from ⟨hxX, hfix⟩)
    have hFE : F ≤ E := hF_sub.trans hXE
    have hFX : F = X := by
      by_contra hne
      exact hXmin F ⟨hTltF, hFE, hFPn⟩ (lt_of_le_of_ne hF_sub hne)
    intro q hq e he
    have heF : e ∈ F := by rw [hFX]; exact he
    exact (show e ∈ X ∧ ∀ q ∈ pCoreOf 2 P, ⁅q, e⁆ ∈ T from heF).2 q hq
  have hcomm : ⁅X, X⁆ ≤ T :=
    Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
      hKT (hEEK (Subgroup.commutator_mem_commutator (hXE hg₁) (hXE hg₂)))
  have hsec' : IsElemSec T X :=
    show T ≤ X ∧ ⁅X, X⁆ ≤ T ∧ ∀ e ∈ X, e ^ 2 ∈ T from ⟨hTX.le, hcomm, hsq⟩
  have h1 : K.relIndex T * T.relIndex E = K.relIndex E :=
    Subgroup.relIndex_mul_relIndex K T E hKT hTE
  have h2 : T.relIndex X * X.relIndex E = T.relIndex E :=
    Subgroup.relIndex_mul_relIndex T X E hTX.le hXE
  have hcard' : T.relIndex X ≤ 16 := by
    have hdvd : T.relIndex X ∣ K.relIndex E :=
      ⟨K.relIndex T * X.relIndex E, by rw [← h1, ← h2]; ring⟩
    exact le_trans (Nat.le_of_dvd (ChiefOfA5.relIndex_pos_of_le hKE) hdvd) hcard
  have hA : A5Chief P L X T := faithful_a5 hLP hPL hXP hPX hPTn hsec' hcard' hq hcore hnt'
  have h3 : K.relIndex T * (T.relIndex X * X.relIndex E) ≤ 16 := by
    rw [h2, h1]; exact hcard
  rw [hA.card] at h3
  have ha : 0 < K.relIndex T := ChiefOfA5.relIndex_pos_of_le hKT
  have hb : 0 < X.relIndex E := ChiefOfA5.relIndex_pos_of_le hXE
  have ha1 : K.relIndex T = 1 := by nlinarith
  have hb1 : X.relIndex E = 1 := by nlinarith
  have hTK : T = K := le_antisymm (Subgroup.relIndex_eq_one.mp ha1) hKT
  have hXE' : X = E := le_antisymm hXE (Subgroup.relIndex_eq_one.mp hb1)
  rw [hXE', hTK] at hA
  exact hA

end CFSG.GH74.QTGen4.DSGen4

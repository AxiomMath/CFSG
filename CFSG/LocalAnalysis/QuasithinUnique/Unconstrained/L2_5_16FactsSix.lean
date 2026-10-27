module

public import Mathlib
public meta import Mathlib
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSixInputs
public import Certificates.Certificate4051

public section

namespace CFSG.QuasithinUnique.Unc25K1.Six

open Equiv

namespace R6

theorem get_enc (σ : P6) (i : Fin 6) : (enc σ).get i = σ i := by
  fin_cases i <;> rfl

theorem enc_mul (σ τ : P6) : enc (σ * τ) = enc σ * enc τ := by
  show enc (σ * τ) = ⟨(enc σ).get (τ 0), (enc σ).get (τ 1), (enc σ).get (τ 2),
    (enc σ).get (τ 3), (enc σ).get (τ 4), (enc σ).get (τ 5)⟩
  simp only [get_enc]
  rfl

theorem enc_inj : Function.Injective enc := by
  intro σ τ h
  refine Equiv.ext fun i => ?_
  have := congrArg (fun r => r.get i) h
  simpa only [get_enc] using this

theorem enc_one : enc 1 = 1 := by decide

end R6

theorem closedB_spec {R : Type*} [One R] [Mul R] [DecidableEq R] {gens L : List R}
    (h : closedB gens L = true) : (1 : R) ∈ L ∧ ∀ x ∈ L, ∀ g ∈ gens, x * g ∈ L := by
  simp only [closedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, fun x hx g hg => h.2 x hx g hg⟩

structure IsEnc {G R : Type*} [Group G] [Mul R] [One R] (enc : G → R) : Prop where
  inj : Function.Injective enc
  map_mul : ∀ x y, enc (x * y) = enc x * enc y
  map_one : enc 1 = 1

theorem iterL_sound {G R : Type*} [Group G] [Mul R] [One R] [DecidableEq R] {enc : G → R}
    (h : IsEnc enc) (gens : List G) (n : ℕ) :
    ∀ r ∈ iterL (gens.map enc) n, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = r := by
  induction n with
  | zero =>
    intro r hr
    simp only [iterL, List.mem_singleton] at hr
    exact ⟨1, Subgroup.one_mem _, by rw [hr, h.map_one]⟩
  | succ n ih =>
    intro r hr
    simp only [iterL, stepL, List.mem_append, List.mem_dedup, List.mem_filter, List.mem_flatMap,
      List.mem_map] at hr
    rcases hr with hr | ⟨⟨y, hy, g', ⟨g, hg, rfl⟩, rfl⟩, -⟩
    · exact ih r hr
    · obtain ⟨x, hx, rfl⟩ := ih y hy
      exact ⟨x * g, Subgroup.mul_mem _ hx (Subgroup.subset_closure hg), h.map_mul x g⟩

theorem mem_closure_iff_of_closed {G R : Type*} [Group G] [Finite G] [Mul R] [One R]
    [DecidableEq R] {enc : G → R} (h : IsEnc enc) (gens : List G) (L : List R)
    (h1 : (1 : R) ∈ L) (hcl : ∀ x ∈ L, ∀ g ∈ gens.map enc, x * g ∈ L)
    (hs : ∀ r ∈ L, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = r) (x : G) :
    x ∈ Subgroup.closure {g | g ∈ gens} ↔ enc x ∈ L := by
  constructor
  · intro hx
    have hsub : (Subgroup.closure {g | g ∈ gens}).toSubmonoid =
        Submonoid.closure {g | g ∈ gens} := Subgroup.closure_toSubmonoid_of_finite
    have hx' : x ∈ Submonoid.closure {g | g ∈ gens} := by rw [← hsub]; exact hx
    refine Submonoid.closure_induction_right (motive := fun m _ => enc m ∈ L)
      (by rwa [h.map_one]) ?_ hx'
    intro m _ y hy hm
    rw [h.map_mul]
    exact hcl _ hm _ (List.mem_map_of_mem hy)
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hs _ hx
    rwa [← h.inj hyx]

theorem card_of_list {G R : Type*} [Group G] [DecidableEq R] {enc : G → R}
    (hinj : Function.Injective enc) (Y : Subgroup G) (L : List R) (hnd : L.Nodup)
    (hY : ∀ x, x ∈ Y ↔ enc x ∈ L) (hs : ∀ r ∈ L, ∃ x, enc x = r) : Nat.card Y = L.length := by
  have e : Y ≃ {r // r ∈ L.toFinset} :=
    Equiv.ofBijective (fun y => ⟨enc y, List.mem_toFinset.2 ((hY y).1 y.2)⟩)
      ⟨fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab)),
      fun ⟨r, hr⟩ => by
        obtain ⟨x, hx⟩ := hs r (List.mem_toFinset.1 hr)
        exact ⟨⟨x, (hY x).2 (hx ▸ List.mem_toFinset.1 hr)⟩, Subtype.ext hx⟩⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

theorem rawIsEnc : IsEnc R6.enc := ⟨R6.enc_inj, R6.enc_mul, R6.enc_one⟩

theorem sizes_ok :
    d0L.length = 8 ∧ saL.length = 24 ∧ sbL.length = 24 ∧ d0L.Nodup ∧ saL.Nodup ∧
    sbL.Nodup :=
  Certificates.certificate4051.1

theorem closed_ok : closedB (d0Gens.map R6.enc) d0L = true ∧
    closedB (saGens.map R6.enc) saL = true ∧ closedB (sbGens.map R6.enc) sbL = true :=
  Certificates.certificate4051.2.1

theorem cover_ok :
    ∀ x : P6, Perm.sign x = 1 → R6.enc x ∈ saL ∨ R6.enc x ∈ sbL ∨
    ∃ r ∈ repsP, ∃ d ∈ d0L, ∃ e ∈ d0L, R6.enc x = d * R6.enc r * e :=
  Certificates.certificate4051.2.2.1

theorem reps_ok :
    ∀ x : P6, Perm.sign x = 1 → ∀ L ∈ repLs, R6.enc x ∈ L :=
  Certificates.certificate4051.2.2.2.1

theorem norm_ok :
    ∀ τ : P6, (d0Gens.map R6.enc).all (conjIn (R6.enc τ) d0L) = true →
    (saGens.map R6.enc).all (conjIn (R6.enc τ) saL) = true ∧
    (sbGens.map R6.enc).all (conjIn (R6.enc τ) sbL) = true :=
  Certificates.certificate4051.2.2.2.2

theorem gens_even : (∀ g ∈ d0Gens, Perm.sign g = 1) ∧ (∀ g ∈ saGens, Perm.sign g = 1) ∧
    (∀ g ∈ sbGens, Perm.sign g = 1) := by
  decide +kernel

abbrev A6s : Subgroup P6 := alternatingGroup (Fin 6)

def D0 : Subgroup P6 := Subgroup.closure {g | g ∈ d0Gens}

def Sa : Subgroup P6 := Subgroup.closure {g | g ∈ saGens}

def Sb : Subgroup P6 := Subgroup.closure {g | g ∈ sbGens}

theorem sound_D0 : ∀ r ∈ d0L, ∃ x ∈ D0, R6.enc x = r := iterL_sound rawIsEnc d0Gens 4

theorem sound_Sa : ∀ r ∈ saL, ∃ x ∈ Sa, R6.enc x = r := iterL_sound rawIsEnc saGens 5

theorem sound_Sb : ∀ r ∈ sbL, ∃ x ∈ Sb, R6.enc x = r := iterL_sound rawIsEnc sbGens 5

theorem mem_D0 (x : P6) : x ∈ D0 ↔ R6.enc x ∈ d0L := by
  obtain ⟨h1, hcl⟩ := closedB_spec closed_ok.1
  exact mem_closure_iff_of_closed rawIsEnc d0Gens d0L h1 hcl sound_D0 x

theorem mem_Sa (x : P6) : x ∈ Sa ↔ R6.enc x ∈ saL := by
  obtain ⟨h1, hcl⟩ := closedB_spec closed_ok.2.1
  exact mem_closure_iff_of_closed rawIsEnc saGens saL h1 hcl sound_Sa x

theorem mem_Sb (x : P6) : x ∈ Sb ↔ R6.enc x ∈ sbL := by
  obtain ⟨h1, hcl⟩ := closedB_spec closed_ok.2.2
  exact mem_closure_iff_of_closed rawIsEnc sbGens sbL h1 hcl sound_Sb x

theorem card_D0 : Nat.card D0 = 8 := by
  rw [card_of_list R6.enc_inj D0 d0L sizes_ok.2.2.2.1 mem_D0
    (fun r hr => (sound_D0 r hr).imp fun x hx => hx.2)]
  exact sizes_ok.1

theorem card_Sa : Nat.card Sa = 24 := by
  rw [card_of_list R6.enc_inj Sa saL sizes_ok.2.2.2.2.1 mem_Sa
    (fun r hr => (sound_Sa r hr).imp fun x hx => hx.2)]
  exact sizes_ok.2.1

theorem card_Sb : Nat.card Sb = 24 := by
  rw [card_of_list R6.enc_inj Sb sbL sizes_ok.2.2.2.2.2 mem_Sb
    (fun r hr => (sound_Sb r hr).imp fun x hx => hx.2)]
  exact sizes_ok.2.2.1

theorem D0_le_Sa : D0 ≤ Sa := Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem D0_le_Sb : D0 ≤ Sb := Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem D0_le_A6 : D0 ≤ A6s := by
  rw [D0, Subgroup.closure_le]
  intro g hg
  exact Equiv.Perm.mem_alternatingGroup.2 (gens_even.1 g hg)

theorem card_A6 : Nat.card A6s = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem A6_le_closure (r : P6) (hr : r ∈ repsP) :
    A6s ≤ Subgroup.closure {g | g ∈ d0Gens ++ [r]} := by
  intro x hx
  have hL : iterL ((d0Gens ++ [r]).map R6.enc) 11 ∈ repLs := List.mem_map_of_mem hr
  have hmem := reps_ok x (Equiv.Perm.mem_alternatingGroup.1 hx) _ hL
  obtain ⟨z, hz, hzx⟩ := iterL_sound rawIsEnc (d0Gens ++ [r]) 11 _ hmem
  rwa [← R6.enc_inj hzx]

theorem union_le {G : Type*} [Group G] {Y A B : Subgroup G} (h : ∀ y ∈ Y, y ∈ A ∨ y ∈ B) :
    Y ≤ A ∨ Y ≤ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hA' : ∃ a ∈ Y, a ∉ A := by
    by_contra hh
    push Not at hh
    exact hA hh
  have hB' : ∃ b ∈ Y, b ∉ B := by
    by_contra hh
    push Not at hh
    exact hB hh
  obtain ⟨a, haY, haA⟩ := hA'
  obtain ⟨b, hbY, hbB⟩ := hB'
  have haB : a ∈ B := (h a haY).resolve_left haA
  have hbA : b ∈ A := (h b hbY).resolve_right hbB
  rcases h (a * b) (Y.mul_mem haY hbY) with hab | hab
  · exact haA (by simpa using A.mul_mem hab (A.inv_mem hbA))
  · exact hbB (by simpa using B.mul_mem (B.inv_mem haB) hab)

theorem sandwich {G : Type*} [Group G] [Finite G] {D Y S : Subgroup G} (hDY : D ≤ Y)
    (hYS : Y ≤ S) (hD : Nat.card D = 8) (hS : Nat.card S = 24) : Y = D ∨ Y = S := by
  have h1 : 8 ∣ Nat.card Y := hD ▸ Subgroup.card_dvd_of_le hDY
  have h2 : Nat.card Y ∣ 24 := hS ▸ Subgroup.card_dvd_of_le hYS
  obtain ⟨k, hk⟩ := h1
  have hk3 : k ≤ 3 := by
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  interval_cases k
  · have := Nat.card_pos (α := Y)
    omega
  · left
    exact (Subgroup.eq_of_le_of_card_ge hDY (by omega)).symm
  · exfalso
    rw [hk] at h2
    norm_num at h2
  · right
    exact Subgroup.eq_of_le_of_card_ge hYS (by omega)

theorem mem_map_conj {G : Type*} [Group G] (Y : Subgroup G) (g x : G) :
    x ∈ Y.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Y := by
  have hc : ∀ y, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun y => rfl
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [hc, e]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    rw [hc]
    group

theorem conj_stable_iff {G : Type*} [Group G] [Finite G] (Y : Subgroup G) (τ : G)
    (h : ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) : ∀ p, p ∈ Y ↔ τ * p * τ⁻¹ ∈ Y := by
  intro p
  refine ⟨h p, fun hp => ?_⟩
  have hle : Y.map (MulAut.conj τ).toMonoidHom ≤ Y := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : Y.map (MulAut.conj τ).toMonoidHom = Y :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective])
  have hp' : τ * p * τ⁻¹ ∈ Y.map (MulAut.conj τ).toMonoidHom := by
    rw [heq]
    exact hp
  have h1 := (mem_map_conj Y τ _).1 hp'
  have e : τ⁻¹ * (τ * p * τ⁻¹) * τ = p := by group
  rwa [e] at h1

theorem conj_stable_of_gens {G : Type*} [Group G] (gens : List G) (τ : G)
    (h : ∀ g ∈ gens, τ * g * τ⁻¹ ∈ Subgroup.closure {g | g ∈ gens}) :
    ∀ y ∈ Subgroup.closure {g | g ∈ gens}, τ * y * τ⁻¹ ∈ Subgroup.closure {g | g ∈ gens} := by
  have : Subgroup.closure {g | g ∈ gens} ≤
      (Subgroup.closure {g | g ∈ gens}).comap (MulAut.conj τ).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro g hg
    exact h g hg
  exact fun y hy => this hy

theorem conjIn_iff {Y : Subgroup P6} {L : List R6} (hmem : ∀ x, x ∈ Y ↔ R6.enc x ∈ L)
    (hs : ∀ r ∈ L, ∃ x, R6.enc x = r) (τ g : P6) :
    conjIn (R6.enc τ) L (R6.enc g) = true ↔ τ * g * τ⁻¹ ∈ Y := by
  simp only [conjIn, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy, hyτ⟩
    obtain ⟨y', hy'⟩ := hs y hy
    rw [← hy', ← R6.enc_mul, ← R6.enc_mul] at hyτ
    have h1 := R6.enc_inj hyτ
    have h2 : y' ∈ Y := (hmem y').2 (hy' ▸ hy)
    have h3 : τ * g * τ⁻¹ = y' := by
      rw [mul_inv_eq_iff_eq_mul, h1]
    rwa [h3]
  · intro h
    refine ⟨R6.enc (τ * g * τ⁻¹), (hmem _).1 h, ?_⟩
    rw [← R6.enc_mul, ← R6.enc_mul]
    congr 1
    group

theorem normalizes_Sa_Sb (τ : P6) (h : ∀ p, p ∈ D0 ↔ τ * p * τ⁻¹ ∈ D0) :
    (∀ p, p ∈ Sa ↔ τ * p * τ⁻¹ ∈ Sa) ∧ (∀ p, p ∈ Sb ↔ τ * p * τ⁻¹ ∈ Sb) := by
  have hD : (d0Gens.map R6.enc).all (conjIn (R6.enc τ) d0L) = true := by
    rw [List.all_eq_true]
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    exact (conjIn_iff mem_D0 (fun r hr => (sound_D0 r hr).imp fun x hx => hx.2) τ g).2
      ((h g).1 (Subgroup.subset_closure hg))
  obtain ⟨hA, hB⟩ := norm_ok τ hD
  have gensOf : ∀ {Y : Subgroup P6} {L : List R6} {gens : List P6},
      Y = Subgroup.closure {g | g ∈ gens} → (∀ x, x ∈ Y ↔ R6.enc x ∈ L) →
      (∀ r ∈ L, ∃ x, R6.enc x = r) →
      (gens.map R6.enc).all (conjIn (R6.enc τ) L) = true → ∀ p, p ∈ Y ↔ τ * p * τ⁻¹ ∈ Y := by
    intro Y L gens hY hmem hs hall
    refine conj_stable_iff Y τ ?_
    rw [hY]
    refine conj_stable_of_gens gens τ ?_
    intro g hg
    rw [← hY]
    exact (conjIn_iff hmem hs τ g).1 (List.all_eq_true.1 hall _ (List.mem_map_of_mem hg))
  exact ⟨gensOf rfl mem_Sa (fun r hr => (sound_Sa r hr).imp fun x hx => hx.2) hA,
    gensOf rfl mem_Sb (fun r hr => (sound_Sb r hr).imp fun x hx => hx.2) hB⟩

theorem six_overgroups (Y : Subgroup P6) (hD : D0 ≤ Y) (hA : Y ≤ A6s) :
    Y = D0 ∨ Y = Sa ∨ Y = Sb ∨ Y = A6s := by
  by_cases hall : ∀ y ∈ Y, y ∈ Sa ∨ y ∈ Sb
  · rcases union_le hall with hYa | hYb
    · rcases sandwich hD hYa card_D0 card_Sa with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases sandwich hD hYb card_D0 card_Sb with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
  · push Not at hall
    obtain ⟨y, hyY, hyA, hyB⟩ := hall
    have hmem := cover_ok y (Equiv.Perm.mem_alternatingGroup.1 (hA hyY))
    rcases hmem with h | h | ⟨r, hr, d, hd, e, he, hyr⟩
    · exact absurd ((mem_Sa y).2 h) hyA
    · exact absurd ((mem_Sb y).2 h) hyB
    · obtain ⟨d', hd', rfl⟩ := sound_D0 d hd
      obtain ⟨e', he', rfl⟩ := sound_D0 e he
      have hy : y = d' * r * e' := by
        apply R6.enc_inj
        rw [R6.enc_mul, R6.enc_mul]
        exact hyr
      have hrY : r ∈ Y := by
        have : r = d'⁻¹ * y * e'⁻¹ := by rw [hy]; group
        rw [this]
        exact Y.mul_mem (Y.mul_mem (Y.inv_mem (hD hd')) hyY) (Y.inv_mem (hD he'))
      right; right; right
      refine le_antisymm hA (le_trans (A6_le_closure r hr) ?_)
      rw [Subgroup.closure_le]
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hD (Subgroup.subset_closure hg)
      · rw [List.mem_singleton.1 hg]
        exact hrY

open scoped Pointwise in
theorem exists_conj_of_card_eight {G : Type*} [Group G] [Finite G] {H P Q : Subgroup G}
    (hPH : P ≤ H) (hQH : Q ≤ H) (hPc : Nat.card P = 8) (hQc : Nat.card Q = 8)
    (hH : Nat.card H = 360) : ∃ g ∈ H, Q = P.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardsub : ∀ S : Subgroup G, S ≤ H → Nat.card S = 8 → IsPGroup 2 (S.subgroupOf H) ∧
      ¬ 2 ∣ (S.subgroupOf H).index := by
    intro S hSH hSc
    have h1 : Nat.card (S.subgroupOf H) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv]; exact hSc
    refine ⟨IsPGroup.of_card (n := 3) (by rw [h1]; norm_num), ?_⟩
    have h2 := Subgroup.card_mul_index (S.subgroupOf H)
    rw [h1, hH] at h2
    omega
  obtain ⟨hP2, hPi⟩ := hcardsub P hPH hPc
  obtain ⟨hQ2, hQi⟩ := hcardsub Q hQH hQc
  let P0 : Sylow 2 H := hP2.toSylow hPi
  let Q0 : Sylow 2 H := hQ2.toSylow hQi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P0 Q0
  have hgQ : (Q0 : Subgroup H) = MulAut.conj g • (P.subgroupOf H) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨g, g.2, ?_⟩
  ext x
  constructor
  · intro hx
    have hxQ : (⟨x, hQH hx⟩ : H) ∈ (Q0 : Subgroup H) := hx
    rw [hgQ, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨s, hs, hsx⟩ := hxQ
    refine ⟨s, hs, ?_⟩
    have := congrArg Subtype.val hsx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  · rintro ⟨y, hy, rfl⟩
    have hyH : y ∈ H := hPH hy
    have hyP : (⟨y, hyH⟩ : H) ∈ P.subgroupOf H := hy
    have := Subgroup.smul_mem_pointwise_smul (⟨y, hyH⟩ : H) (MulAut.conj g) _ hyP
    rw [← hgQ] at this
    exact this

theorem sign_conj (g x : P6) : Perm.sign (g * x * g⁻¹) = Perm.sign x := by
  rw [map_mul, map_mul, map_inv, mul_comm (Perm.sign g) (Perm.sign x), mul_assoc, mul_inv_cancel,
    mul_one]

theorem mem_A6_conj (g x : P6) : g * x * g⁻¹ ∈ A6s ↔ x ∈ A6s := by
  simp only [Equiv.Perm.mem_alternatingGroup, sign_conj]

theorem six_key {P' X' : Subgroup P6} (hPc : Nat.card P' = 8) (hPA : P' ≤ A6s) (hPX : P' ≤ X')
    (hXA : X' ≤ A6s) (hXP : X' ≠ P') (hXA' : X' ≠ A6s) (τ : P6)
    (hτ : ∀ p, p ∈ P' ↔ τ * p * τ⁻¹ ∈ P') : ∀ p, p ∈ X' ↔ τ * p * τ⁻¹ ∈ X' := by
  obtain ⟨g, hg, hPg⟩ := exists_conj_of_card_eight (H := A6s) D0_le_A6 hPA card_D0 hPc card_A6
  have hP'mem : ∀ x, x ∈ P' ↔ g⁻¹ * x * g ∈ D0 := fun x => by
    rw [hPg]
    exact mem_map_conj D0 g x
  let Z : Subgroup P6 := X'.comap (MulAut.conj g).toMonoidHom
  have hZmem : ∀ x, x ∈ Z ↔ g * x * g⁻¹ ∈ X' := fun x => Iff.rfl
  have hX'Z : ∀ x, x ∈ X' ↔ g⁻¹ * x * g ∈ Z := fun x => by
    rw [hZmem]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
  have hD0Z : D0 ≤ Z := by
    intro d hd
    rw [hZmem]
    apply hPX
    rw [hP'mem]
    have e : g⁻¹ * (g * d * g⁻¹) * g = d := by group
    rw [e]
    exact hd
  have hZA : Z ≤ A6s := by
    intro z hz
    exact (mem_A6_conj g z).1 (hXA ((hZmem z).1 hz))
  have hZne1 : Z ≠ D0 := by
    intro hZ
    apply hXP
    ext x
    rw [hX'Z, hZ, hP'mem]
  have hZne2 : Z ≠ A6s := by
    intro hZ
    apply hXA'
    ext x
    rw [hX'Z, hZ]
    have := mem_A6_conj g⁻¹ x
    rwa [inv_inv] at this
  have hZ : Z = Sa ∨ Z = Sb := by
    rcases six_overgroups Z hD0Z hZA with h | h | h | h
    · exact absurd h hZne1
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hZne2
  have hτD0 : ∀ p, p ∈ D0 ↔ (g⁻¹ * τ * g) * p * (g⁻¹ * τ * g)⁻¹ ∈ D0 := by
    intro p
    have e1 : p ∈ D0 ↔ g * p * g⁻¹ ∈ P' := by
      rw [hP'mem]
      have e : g⁻¹ * (g * p * g⁻¹) * g = p := by group
      rw [e]
    have e4 : (g⁻¹ * τ * g) * p * (g⁻¹ * τ * g)⁻¹ = g⁻¹ * (τ * (g * p * g⁻¹) * τ⁻¹) * g := by
      group
    rw [e4, ← hP'mem, ← hτ, e1]
  obtain ⟨hSa, hSb⟩ := normalizes_Sa_Sb (g⁻¹ * τ * g) hτD0
  have hZstab : ∀ x, x ∈ Z ↔ (g⁻¹ * τ * g) * x * (g⁻¹ * τ * g)⁻¹ ∈ Z := by
    rcases hZ with h | h <;> rw [h] <;> assumption
  intro p
  rw [hX'Z p, hX'Z (τ * p * τ⁻¹), hZstab]
  have e5 : (g⁻¹ * τ * g) * (g⁻¹ * p * g) * (g⁻¹ * τ * g)⁻¹ = g⁻¹ * (τ * p * τ⁻¹) * g := by
    group
  rw [e5]

end CFSG.QuasithinUnique.Unc25K1.Six

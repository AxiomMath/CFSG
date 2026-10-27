module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Fused

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B : Subgroup G} {z : G}

omit [Finite G] in
theorem conj_inv_toMonoidHom_apply (g x : G) :
    (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by simp

theorem mem_iff_conj_of_conj_le (S : Subgroup G) {g : G} (h : ∀ s ∈ S, g⁻¹ * s * g ∈ S) :
    ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S := by
  have hinj : Function.Injective (fun s : S => (⟨g⁻¹ * s * g, h s s.2⟩ : S)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.surjective_of_injective hinj
  intro s
  constructor
  · intro hs
    obtain ⟨s₁, hs₁⟩ := hsurj ⟨s, hs⟩
    have this : g⁻¹ * (s₁ : G) * g = s := congrArg Subtype.val hs₁
    have e : g * s * g⁻¹ = s₁ := by
      rw [← this]
      group
    rw [e]
    exact s₁.2
  · intro hs
    have := h _ hs
    simpa [mul_assoc] using this

omit [Finite G] in
theorem ThLocalIn.conj_mem_A {L : Subgroup G} (W : ThLocalIn L S A B z) {g : G}
    (hg : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S) {x : G} (hx : x ∈ A) : g * x * g⁻¹ ∈ A := by
  rw [W.mem_A_iff] at hx ⊢
  obtain ⟨hxS, hx4⟩ := hx
  refine ⟨(hg x).1 hxS, fun s₁ hs₁ s₂ hs₂ s₃ hs₃ s₄ hs₄ => ?_⟩
  have key : ∀ (u v : G), ⁅g * u * g⁻¹, g * v * g⁻¹⁆ = g * ⁅u, v⁆ * g⁻¹ := fun u v => by
    simp only [commutatorElement_def]
    group
  have hS' : ∀ s ∈ S, g⁻¹ * s * g ∈ S := fun s hs => by
    refine (hg _).2 ?_
    simpa [mul_assoc] using hs
  have h := hx4 (g⁻¹ * s₁ * g) (hS' _ hs₁) (g⁻¹ * s₂ * g) (hS' _ hs₂) (g⁻¹ * s₃ * g) (hS' _ hs₃)
    (g⁻¹ * s₄ * g) (hS' _ hs₄)
  have e : ∀ s : G, s = g * (g⁻¹ * s * g) * g⁻¹ := fun s => by group
  rw [e s₁, e s₂, e s₃, e s₄, key, key, key, key, h]
  group

theorem ThLocalIn.conj_inv_mem_A {L : Subgroup G} (W : ThLocalIn L S A B z) {g : G}
    (hg : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S) {x : G} (hx : x ∈ A) : g⁻¹ * x * g ∈ A := by
  have hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun a ha => W.conj_mem_A hg ha
  have := mem_iff_conj_of_conj_le A (g := g⁻¹) (fun a ha => by simpa using hA a ha)
  have h2 := (this x).1 hx
  simpa using h2

omit [Finite G] in
theorem conj_inv_mem_of_conj_mem {A : Subgroup G} [Finite G] {n : G} (hn : ∀ x ∈ A, n * x * n⁻¹ ∈ A)
    {x : G} (hx : x ∈ A) : n⁻¹ * x * n ∈ A := by
  have := mem_iff_conj_of_conj_le A (g := n⁻¹) (fun a ha => by simpa using hn a ha)
  simpa using (this x).1 hx

section Fusing

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z)

include H W

theorem ThCyc.exists_fusing_z :
    ∃ (P : Sylow 2 G) (g : G), S ⊔ R ≤ (P : Subgroup G) ∧ g ∈ (P : Subgroup G) ∧
      g ∈ normalizer ((S ⊔ R : Subgroup G) : Set G) ∧ g ∉ S ⊔ R ∧ g * t * g⁻¹ = z * t := by
  obtain ⟨P, g, hSP, hgP, hgn, hgS, e, he, he1, heZ, hge⟩ :=
    H.exists_fusing_element W.isThSylow
  have hez : e = z := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (W.center_le e he heZ)
    rcases zpow_eq_one_or_self W.z_sq k with h | h
    · exact absurd h he1
    · exact h
  exact ⟨P, g, hSP, hgP, hgn, hgS, by rw [hge, hez]⟩

theorem ThCyc.sup_inf_le {y : G} (hy : y ∈ S ⊔ R) (hyL : y ∈ L) : y ∈ S := by
  obtain ⟨a, ha, r, hr, rfl⟩ := H.exists_mul_of_mem_sylow_sup W.isThSylow hy
  have hrL : r ∈ L := by
    have := L.mul_mem (L.inv_mem (W.S_le ha)) hyL
    simpa using this
  have : r ∈ L ⊓ R := ⟨hrL, hr⟩
  rw [disjoint_iff.1 H.disjoint, mem_bot] at this
  rw [this, mul_one]
  exact ha

theorem ThCyc.normalizes_S {g : G} (hgn : g ∈ normalizer ((S ⊔ R : Subgroup G) : Set G))
    (hgt : g * t * g⁻¹ = z * t) : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzL : z ∈ L := W.S_le W.z_mem
  have hz2 : orderOf (⟨z, hzL⟩ : L) = 2 := by
    refine orderOf_eq_prime (Subtype.ext (by simpa using W.z_sq)) fun h => W.z_ne_one ?_
    simpa using congrArg Subtype.val h
  have hperf := H.data.perfectCentralizer _ hz2
  set Mz : Subgroup G := (centralizer ({⟨z, hzL⟩} : Set L)).map L.subtype with hMz
  have hMzperf : ⁅Mz, Mz⁆ = Mz := by
    rw [hMz, ← Subgroup.map_commutator, hperf]
  have hMzz : ∀ m ∈ Mz, z * m = m * z := by
    rintro _ ⟨y, hy, rfl⟩
    exact (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)).symm
  have hLt : ∀ m ∈ L, t * m = m * t := fun m hm => by
    have : m ∈ centralizer ({t} : Set G) := by
      rw [H.centralizer_eq]
      exact mem_sup_left hm
    exact (mem_centralizer_singleton_iff.1 this).symm
  have hSMz : S ≤ Mz := fun s hs =>
    ⟨⟨s, W.S_le hs⟩, mem_centralizer_singleton_iff.2 (Subtype.ext (W.z_central s hs).symm), rfl⟩
  set M' : Subgroup G := Mz.map (MulAut.conj g⁻¹).toMonoidHom with hM'
  have hM'perf : ⁅M', M'⁆ = M' := by
    rw [hM', ← Subgroup.map_commutator, hMzperf]
  have hM'le : M' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hmL : m ∈ L := by
      obtain ⟨y, -, rfl⟩ := hm
      exact y.2
    have h1 := hMzz m hm
    have h2 := hLt m hmL
    rw [conj_inv_toMonoidHom_apply]
    symm
    have hmzt : m * (z * t) = (z * t) * m := by
      calc m * (z * t) = (m * z) * t := by rw [mul_assoc]
        _ = (z * m) * t := by rw [h1]
        _ = z * (m * t) := by rw [mul_assoc]
        _ = z * (t * m) := by rw [h2]
        _ = (z * t) * m := by rw [mul_assoc]
    have e : t = g⁻¹ * (z * t) * g := by
      rw [← hgt]
      group
    calc t * (g⁻¹ * m * g) = (g⁻¹ * (z * t) * g) * (g⁻¹ * m * g) := congrArg (· * _) e
      _ = g⁻¹ * ((z * t) * m) * g := by group
      _ = g⁻¹ * (m * (z * t)) * g := by rw [hmzt]
      _ = (g⁻¹ * m * g) * (g⁻¹ * (z * t) * g) := by group
      _ = g⁻¹ * m * g * t := by rw [← e]
  have hM'L : M' ≤ L := fun x hx => by
    have hx' : x ∈ ⁅M', M'⁆ := by rw [hM'perf]; exact hx
    exact H.commutator_centralizer_le (Subgroup.commutator_mono hM'le hM'le hx')
  have hconj : ∀ s ∈ S, g⁻¹ * s * g ∈ S := by
    intro s hs
    have hsM' : g⁻¹ * s * g ∈ M' := ⟨s, hSMz hs, conj_inv_toMonoidHom_apply g s⟩
    have hsL : g⁻¹ * s * g ∈ L := hM'L hsM'
    have hsSR : g⁻¹ * s * g ∈ S ⊔ R := by
      have := (mem_normalizer_iff.1 hgn (g⁻¹ * s * g)).2 (by
        have : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
        rw [this]
        exact mem_sup_left hs)
      exact this
    exact H.sup_inf_le W hsSR hsL
  exact mem_iff_conj_of_conj_le S hconj

end Fusing

omit [Finite G] in
@[expose] def W5 (A : Subgroup G) (t : G) : Subgroup G := A ⊔ zpowers t

theorem ThCyc.comm_of_mem_L (H : ThCyc G L R t) {m : G} (hm : m ∈ L) : t * m = m * t := by
  have : m ∈ centralizer ({t} : Set G) := by
    rw [H.centralizer_eq]
    exact mem_sup_left hm
  exact (mem_centralizer_singleton_iff.1 this).symm

theorem ThCyc.sq_t (H : ThCyc G L R t) : t ^ 2 = 1 := by
  rw [← H.order_two]
  exact pow_orderOf_eq_one t

theorem ThCyc.mem_W5_iff (H : ThCyc G L R t) (hA : A ≤ L) {x : G} :
    x ∈ W5 A t ↔ x ∈ A ∨ ∃ a ∈ A, x = a * t := by
  constructor
  · intro hx
    have hc : zpowers t ≤ centralizer (A : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun a ha => (H.comm_of_mem_L (hA ha)).symm
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rcases zpow_eq_one_or_self H.sq_t k with h | h
    · left
      rw [h, mul_one]
      exact ha
    · right
      exact ⟨a, ha, by rw [h]⟩
  · rintro (hx | ⟨a, ha, rfl⟩)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_zpowers t))

section Normalizer

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z)

include H W

theorem ThCyc.exists_conj_mul_t {g : G} (hgt : g * t * g⁻¹ = z * t) {a : G} (ha : a ∈ A) :
    ∃ c : G, c * t * c⁻¹ = a * t := by
  by_cases ha1 : a = 1
  · exact ⟨1, by simp [ha1]⟩
  · obtain ⟨n, hnL, hnA, hnz⟩ := W.trans a ha ha1
    refine ⟨n * g, ?_⟩
    have hnt : n * t * n⁻¹ = t := by
      rw [← H.comm_of_mem_L hnL]
      group
    calc n * g * t * (n * g)⁻¹ = n * (g * t * g⁻¹) * n⁻¹ := by group
      _ = n * (z * t) * n⁻¹ := by rw [hgt]
      _ = (n * z * n⁻¹) * (n * t * n⁻¹) := by group
      _ = a * t := by rw [hnz, hnt]

theorem ThCyc.W5_normalizer_mem {g : G} (hgt : g * t * g⁻¹ = z * t) {r : G}
    (hr : r ∈ normalizer ((W5 A t : Subgroup G) : Set G)) {a : G} (ha : a ∈ A) :
    r * a * r⁻¹ ∈ A := by
  have haW : a ∈ W5 A t := mem_sup_left ha
  have hra : r * a * r⁻¹ ∈ W5 A t := (mem_normalizer_iff.1 hr a).1 haW
  have hA : A ≤ L := le_trans (fun x hx => (W.mem_A_iff x).1 hx |>.1) W.S_le
  rcases (H.mem_W5_iff hA).1 hra with h | ⟨a', ha', h⟩
  · exact h
  · exfalso
    obtain ⟨c, hc⟩ := H.exists_conj_mul_t W hgt ha'
    have h1 : (c⁻¹ * r) * a * (c⁻¹ * r)⁻¹ = t := by
      calc (c⁻¹ * r) * a * (c⁻¹ * r)⁻¹ = c⁻¹ * (r * a * r⁻¹) * c := by group
        _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [h, hc]
        _ = t := by group
    have haL : a ∈ L := W.S_le (((W.mem_A_iff a).1 ha).1)
    apply H.not_conj_mem (c⁻¹ * r)
    have : (c⁻¹ * r)⁻¹ * t * (c⁻¹ * r) = a := by
      rw [← h1]
      group
    rw [this]
    exact haL

theorem ThCyc.mem_normalizer_W5_of_L {n : G} (hnL : n ∈ L) (hn : ∀ x ∈ A, n * x * n⁻¹ ∈ A) :
    n ∈ normalizer ((W5 A t : Subgroup G) : Set G) := by
  have hA : A ≤ L := le_trans (fun x hx => (W.mem_A_iff x).1 hx |>.1) W.S_le
  have hinv : ∀ x ∈ A, n⁻¹ * x * n ∈ A := fun x hx => conj_inv_mem_of_conj_mem hn hx
  have key := mem_iff_conj_of_conj_le (W5 A t) (g := n) (fun w hw => by
    rcases (H.mem_W5_iff hA).1 hw with h | ⟨a, ha, rfl⟩
    · exact mem_sup_left (hinv w h)
    · have hnt : n⁻¹ * t * n = t := by
        rw [← H.comm_of_mem_L (L.inv_mem hnL)]
        group
      have : n⁻¹ * (a * t) * n = (n⁻¹ * a * n) * t := by
        calc n⁻¹ * (a * t) * n = n⁻¹ * a * n * (n⁻¹ * t * n) := by group
          _ = (n⁻¹ * a * n) * t := by rw [hnt]
      rw [this]
      exact mul_mem (mem_sup_left (hinv a ha)) (mem_sup_right (mem_zpowers t)))
  exact mem_normalizer_iff.2 key

theorem ThCyc.exists_translation {g : G} (hgt : g * t * g⁻¹ = z * t)
    (hgS : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S) {a : G} (ha : a ∈ A) :
    ∃ r ∈ normalizer ((W5 A t : Subgroup G) : Set G), r * t * r⁻¹ = a * t ∧
      ∀ x ∈ A, r * x * r⁻¹ = x := by
  have hA : A ≤ L := le_trans (fun x hx => (W.mem_A_iff x).1 hx |>.1) W.S_le
  have hgA : ∀ x ∈ A, g * x * g⁻¹ ∈ A := fun x hx => W.conj_mem_A hgS hx
  have hgA' : ∀ x ∈ A, g⁻¹ * x * g ∈ A := fun x hx => W.conj_inv_mem_A hgS hx
  obtain ⟨n, hnL, hn⟩ := W.surj (fun y => g⁻¹ * y * g) (fun x hx => hgA' x hx)
    (fun x hx y hy => by group)
    (fun x hx y hy hxy => by simpa using hxy)
  have hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A := fun x hx => by rw [hn x hx]; exact hgA' x hx
  set r₀ : G := g * n with hr₀
  have hr₀A : ∀ x ∈ A, r₀ * x * r₀⁻¹ = x := fun x hx => by
    have : r₀ * x * r₀⁻¹ = g * (n * x * n⁻¹) * g⁻¹ := by rw [hr₀]; group
    rw [this, hn x hx]
    group
  have hnt : n * t * n⁻¹ = t := by
    rw [← H.comm_of_mem_L hnL]
    group
  have hr₀t : r₀ * t * r₀⁻¹ = z * t := by
    have : r₀ * t * r₀⁻¹ = g * (n * t * n⁻¹) * g⁻¹ := by rw [hr₀]; group
    rw [this, hnt, hgt]
  have hzA : z ∈ A := W.z_mem_A
  have hr₀A' : ∀ x ∈ A, r₀⁻¹ * x * r₀ = x := fun x hx =>
    calc r₀⁻¹ * x * r₀ = r₀⁻¹ * (r₀ * x * r₀⁻¹) * r₀ := by rw [hr₀A x hx]
      _ = x := by group
  have hr₀N : r₀ ∈ normalizer ((W5 A t : Subgroup G) : Set G) := by
    have key := mem_iff_conj_of_conj_le (W5 A t) (g := r₀) (fun w hw => by
      rcases (H.mem_W5_iff hA).1 hw with h | ⟨a', ha', rfl⟩
      · rw [hr₀A' w h]
        exact mem_sup_left h
      · have h2 : r₀⁻¹ * t * r₀ = z * t := by
          have hzt : r₀⁻¹ * (z * t) * r₀ = t := by
            rw [← hr₀t]
            group
          calc r₀⁻¹ * t * r₀ = r₀⁻¹ * (z * (z * t)) * r₀ := by
                have : z * (z * t) = t := by
                  rw [← mul_assoc, ← sq, W.z_sq, one_mul]
                rw [this]
            _ = (r₀⁻¹ * z * r₀) * (r₀⁻¹ * (z * t) * r₀) := by group
            _ = z * t := by rw [hr₀A' z hzA, hzt]
        have : r₀⁻¹ * (a' * t) * r₀ = a' * (z * t) := by
          calc r₀⁻¹ * (a' * t) * r₀ = (r₀⁻¹ * a' * r₀) * (r₀⁻¹ * t * r₀) := by group
            _ = a' * (z * t) := by rw [hr₀A' a' ha', h2]
        rw [this]
        exact mul_mem (mem_sup_left ha')
          (mul_mem (mem_sup_left hzA) (mem_sup_right (mem_zpowers t))))
    exact mem_normalizer_iff.2 key
  by_cases ha1 : a = 1
  · exact ⟨1, one_mem _, by simp [ha1], fun x _ => by simp⟩
  · obtain ⟨m, hmL, hmA, hmz⟩ := W.trans a ha ha1
    have hmA' : ∀ x ∈ A, m⁻¹ * x * m ∈ A := fun x hx => conj_inv_mem_of_conj_mem hmA hx
    have hmN := H.mem_normalizer_W5_of_L W hmL hmA
    refine ⟨m * r₀ * m⁻¹, mul_mem (mul_mem hmN hr₀N) (inv_mem hmN), ?_, fun x hx => ?_⟩
    · have hmt : m * t * m⁻¹ = t := by
        rw [← H.comm_of_mem_L hmL]
        group
      have hmt' : m⁻¹ * t * m = t := by
        rw [← H.comm_of_mem_L (L.inv_mem hmL)]
        group
      calc m * r₀ * m⁻¹ * t * (m * r₀ * m⁻¹)⁻¹ = m * (r₀ * (m⁻¹ * t * m) * r₀⁻¹) * m⁻¹ := by group
        _ = m * (z * t) * m⁻¹ := by rw [hmt', hr₀t]
        _ = (m * z * m⁻¹) * (m * t * m⁻¹) := by group
        _ = a * t := by rw [hmz, hmt]
    · have : m * r₀ * m⁻¹ * x * (m * r₀ * m⁻¹)⁻¹ = m * (r₀ * (m⁻¹ * x * m) * r₀⁻¹) * m⁻¹ := by
        group
      rw [this, hr₀A _ (hmA' x hx)]
      group

theorem ThCyc.mem_centralizer_W5_iff {y : G} :
    y ∈ centralizer ((W5 A t : Subgroup G) : Set G) ↔ ∃ b ∈ B, ∃ k : ℤ, y = b * t ^ k := by
  have hA : A ≤ L := le_trans (fun x hx => (W.mem_A_iff x).1 hx |>.1) W.S_le
  have hAt : ∀ a ∈ A, ∀ k : ℤ, a * t ^ k = t ^ k * a := fun a ha k =>
    ((show Commute a t from (H.comm_of_mem_L (hA ha)).symm).zpow_right k).eq
  constructor
  · intro hy
    have hy' := mem_centralizer_iff.1 hy
    have hyt : t * y = y * t := hy' t (mem_sup_right (mem_zpowers t))
    have hyC : y ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hyt.symm
    rw [H.centralizer_eq, H.eq_zpowers] at hyC
    obtain ⟨l, hl, r, hr, rfl⟩ :=
      exists_mul_of_mem_sup (by rw [← H.eq_zpowers]; exact H.le_centralizer) hyC
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    refine ⟨l, (W.mem_B_iff l hl).2 fun a ha => ?_, k, rfl⟩
    have h1 := hy' a (mem_sup_left ha)
    have h2 : a * l * t ^ k = l * a * t ^ k := by
      calc a * l * t ^ k = a * (l * t ^ k) := by rw [mul_assoc]
        _ = l * t ^ k * a := h1
        _ = l * (t ^ k * a) := by rw [mul_assoc]
        _ = l * (a * t ^ k) := by rw [hAt a ha k]
        _ = l * a * t ^ k := by rw [mul_assoc]
    exact (mul_right_cancel h2).symm
  · rintro ⟨b, hb, k, rfl⟩
    refine mem_centralizer_iff.2 fun w hw => ?_
    have hbL : b ∈ L := W.B_le hb
    have hbA := (W.mem_B_iff b hbL).1 hb
    have hbt : b * t ^ k * t = t * (b * t ^ k) := by
      have h1 : t * b = b * t := H.comm_of_mem_L hbL
      calc b * t ^ k * t = b * t * t ^ k := by
            rw [mul_assoc, mul_assoc, ← zpow_one_add, ← zpow_add_one, add_comm]
        _ = t * b * t ^ k := by rw [h1]
        _ = t * (b * t ^ k) := by rw [mul_assoc]
    rcases (H.mem_W5_iff hA).1 hw with h | ⟨a, ha, rfl⟩
    · calc w * (b * t ^ k) = (w * b) * t ^ k := by rw [mul_assoc]
        _ = (b * w) * t ^ k := by rw [(hbA w h).symm]
        _ = b * (w * t ^ k) := by rw [mul_assoc]
        _ = b * (t ^ k * w) := by rw [hAt w h k]
        _ = b * t ^ k * w := by rw [mul_assoc]
    · calc a * t * (b * t ^ k) = a * (t * (b * t ^ k)) := by rw [mul_assoc]
        _ = a * (b * t ^ k * t) := by rw [hbt]
        _ = (a * (b * t ^ k)) * t := (mul_assoc _ _ _).symm
        _ = (b * t ^ k * a) * t := by
            congr 1
            calc a * (b * t ^ k) = (a * b) * t ^ k := by rw [mul_assoc]
              _ = (b * a) * t ^ k := by rw [(hbA a ha).symm]
              _ = b * (a * t ^ k) := by rw [mul_assoc]
              _ = b * (t ^ k * a) := by rw [hAt a ha k]
              _ = b * t ^ k * a := by rw [mul_assoc]
        _ = b * t ^ k * (a * t) := by rw [mul_assoc]

end Normalizer

end CFSG.EvenSporadicStandard.ThStd

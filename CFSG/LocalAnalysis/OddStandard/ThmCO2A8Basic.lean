module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8Defs

public section

namespace CFSG.OddStandard.ThmC.O2.A8

open CFSG Subgroup

section BasicAux

variable {K : Type} [Group K] {A : Type} [Group A] {ρ : K →* MulAut A} {V : Sylow 2 K}
  {Z : Subgroup A}

theorem b1_act_mul (ρ : K →* MulAut A) (x y : K) (a : A) : ρ (x * y) a = ρ x (ρ y a) := by
  rw [map_mul]; rfl

theorem b1_act_inv_act (ρ : K →* MulAut A) (k : K) (a : A) : ρ k⁻¹ (ρ k a) = a := by
  rw [← b1_act_mul, inv_mul_cancel, map_one]; rfl

theorem b1_act_act_inv (ρ : K →* MulAut A) (k : K) (a : A) : ρ k (ρ k⁻¹ a) = a := by
  rw [← b1_act_mul, mul_inv_cancel, map_one]; rfl

theorem b1_inv (h : Hyp ρ V Z) (a : A) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.sq a)

theorem b1_mem_smul (k x : K) :
    x ∈ (k • V : Sylow 2 K) ↔ k⁻¹ * x * k ∈ (V : Subgroup K) := by
  show x ∈ ((k • V : Sylow 2 K) : Subgroup K) ↔ _
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

theorem b1_mem_map (ρ : K →* MulAut A) (Z : Subgroup A) (k : K) (a : A) :
    a ∈ Z.map (ρ k).toMonoidHom ↔ ρ k⁻¹ a ∈ Z := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : ρ k⁻¹ ((ρ k).toMonoidHom x) = x := b1_act_inv_act ρ k x
    rwa [this]
  · intro ha
    exact ⟨ρ k⁻¹ a, ha, b1_act_act_inv ρ k a⟩

theorem b1_comm_mem (h : Hyp ρ V Z) {v : K} (hv : v ∈ (V : Subgroup K)) (hv1 : v ≠ 1) (a : A) :
    ρ v a * a⁻¹ ∈ Z := by
  rw [← h.fix v hv hv1]
  have hvv : ρ v (ρ v a) = a := by
    rw [← b1_act_mul, h.sqV v hv, map_one]; rfl
  rw [map_mul, map_inv, hvv]
  simp only [b1_inv h]
  exact h.comm _ _

def b1_H (ρ : K →* MulAut A) (Z : Subgroup A) : Subgroup K where
  carrier := {g | (∀ a ∈ Z, ρ g a = a) ∧ ∀ a : A, ρ g a * a⁻¹ ∈ Z}
  one_mem' := ⟨fun a _ => by simp, fun a => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun a ha => ?_, fun a => ?_⟩
    · rw [b1_act_mul, hy1 a ha, hx1 a ha]
    · rw [b1_act_mul]
      simpa [mul_assoc] using Z.mul_mem (hx2 (ρ y a)) (hy2 a)
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun a ha => ?_, fun a => ?_⟩
    · have h1 := b1_act_inv_act ρ x a
      rwa [hx1 a ha] at h1
    · have h1 := hx2 (ρ x⁻¹ a)
      rw [b1_act_act_inv] at h1
      simpa using Z.inv_mem h1

theorem b1_H_sq (h : Hyp ρ V Z) {g : K} (hg : g ∈ b1_H ρ Z) : g * g = 1 := by
  obtain ⟨h1, h2⟩ := hg
  apply h.inj
  ext a
  set z := ρ g a * a⁻¹ with hz
  have hza : z * a = ρ g a := inv_mul_cancel_right _ _
  have hgz : ρ g z = z := h1 z (h2 a)
  calc ρ (g * g) a = ρ g (ρ g a) := b1_act_mul ρ g g a
    _ = ρ g (z * a) := by rw [hza]
    _ = ρ g z * ρ g a := map_mul _ _ _
    _ = z * (z * a) := by rw [hgz, hza]
    _ = (z * z) * a := (mul_assoc _ _ _).symm
    _ = a := by rw [h.sq z, one_mul]
    _ = (ρ 1) a := by rw [map_one]; rfl

theorem b1_H_isPGroup (h : Hyp ρ V Z) : IsPGroup 2 (b1_H ρ Z) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  show (g : K) ^ 2 ^ 1 = 1
  rw [pow_one, pow_two]
  exact b1_H_sq h g.2

theorem b1_le (h : Hyp ρ V Z) : (V : Subgroup K) ≤ b1_H ρ Z := by
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]; exact (b1_H ρ Z).one_mem
  · exact ⟨fun a ha => (h.fix v hv hv1 a).2 ha, fun a => b1_comm_mem h hv hv1 a⟩

theorem b1_exists_ne (h : Hyp ρ V Z) : ∃ v ∈ (V : Subgroup K), v ≠ 1 := by
  have hne : (V : Subgroup K) ≠ ⊥ := by
    intro hbot
    have h4 := h.cardV
    rw [hbot, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  exact ⟨v, hv, fun h' => hv1 (Subtype.ext h')⟩

theorem b1_imp_stab (h : Hyp ρ V Z) {k : K}
    (hk : k ∈ normalizer ((V : Subgroup K) : Set K)) : ∀ a ∈ Z, ρ k a ∈ Z := by
  intro a ha
  obtain ⟨v, hv, hv1⟩ := b1_exists_ne h
  have hw : k⁻¹ * v * k ∈ (V : Subgroup K) := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hk) v).1 hv
    simpa using this
  have hw1 : k⁻¹ * v * k ≠ 1 := by
    intro h1; apply hv1
    have : v = k * (k⁻¹ * v * k) * k⁻¹ := by group
    rw [this, h1]; group
  have h3 : ρ (k * (k⁻¹ * v * k)) a = ρ k a := by
    rw [b1_act_mul, (h.fix _ hw hw1 a).2 ha]
  have h4 : k * (k⁻¹ * v * k) = v * k := by group
  rw [h4, b1_act_mul] at h3
  exact (h.fix v hv hv1 _).1 h3

end BasicAux

section BasicAuxFinite

variable {K : Type} [Group K] [Finite K] {A : Type} [Group A] {ρ : K →* MulAut A}
  {V : Sylow 2 K} {Z : Subgroup A}

theorem b1_conj (h : Hyp ρ V Z) (k : K) : Hyp ρ (k • V) (Z.map (ρ k).toMonoidHom) where
  comm := h.comm
  sq := h.sq
  cardA := h.cardA
  inj := h.inj
  cardV := by
    have h1 := Sylow.card_eq_multiplicity V
    have h2 := Sylow.card_eq_multiplicity (k • V)
    exact (h2.trans h1.symm).trans h.cardV
  sqV := by
    intro v hv
    have hv' := h.sqV _ ((b1_mem_smul k v).1 hv)
    have : v * v = k * ((k⁻¹ * v * k) * (k⁻¹ * v * k)) * k⁻¹ := by group
    rw [this, hv']; group
  cardZ := by
    rw [Subgroup.card_map_of_injective (ρ k).injective]; exact h.cardZ
  fix := by
    intro v hv hv1 a
    have hv' := (b1_mem_smul k v).1 hv
    have hv1' : k⁻¹ * v * k ≠ 1 := by
      intro h1; apply hv1
      have : v = k * (k⁻¹ * v * k) * k⁻¹ := by group
      rw [this, h1]; group
    rw [b1_mem_map, ← h.fix _ hv' hv1']
    have h1 : ρ (k⁻¹ * v * k) (ρ k⁻¹ a) = ρ k⁻¹ (ρ v a) := by
      rw [← b1_act_mul, ← b1_act_mul]
      congr 2
      group
    rw [h1]
    exact (ρ k⁻¹).injective.eq_iff.symm
  notinv := by
    intro hinv
    apply h.notinv
    intro k' a ha
    have h1 : ρ k a ∈ Z.map (ρ k).toMonoidHom := Subgroup.mem_map_of_mem _ ha
    have h2 := (b1_mem_map ρ Z k _).1 (hinv (k * k' * k⁻¹) _ h1)
    have e : ρ k⁻¹ (ρ (k * k' * k⁻¹) (ρ k a)) = ρ k' a := by
      rw [← b1_act_mul, ← b1_act_mul]
      congr 2
      group
    rwa [e] at h2

end BasicAuxFinite

section BasicAuxFinite2

variable {K : Type} [Group K] [Finite K] {A : Type} [Group A] [Finite A] {ρ : K →* MulAut A}
  {V : Sylow 2 K} {Z : Subgroup A}

theorem b1_stab_imp (h : Hyp ρ V Z) {k : K} (hk : ∀ a ∈ Z, ρ k a ∈ Z) :
    k ∈ normalizer ((V : Subgroup K) : Set K) := by
  have hZ : Z.map (ρ k).toMonoidHom = Z := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hk a ha
    · rw [Subgroup.card_map_of_injective (ρ k).injective]
  have h' : Hyp ρ (k • V) Z := hZ ▸ b1_conj h k
  have h2 : ((k • V : Sylow 2 K) : Subgroup K) ≤ b1_H ρ Z := b1_le h'
  have h3 : b1_H ρ Z = V := V.is_maximal' (b1_H_isPGroup h) (b1_le h)
  have h4 : ((k • V : Sylow 2 K) : Subgroup K) ≤ (V : Subgroup K) := h3 ▸ h2
  have h5 : (V : Subgroup K) = (k • V : Sylow 2 K) := (k • V).is_maximal' V.isPGroup' h4
  exact Sylow.smul_eq_iff_mem_normalizer.1 (Sylow.ext h5).symm

end BasicAuxFinite2

section Basic

variable {K : Type} [Group K] [Finite K] {A : Type} [Group A] [Finite A]
  {ρ : K →* MulAut A} {V : Sylow 2 K} {Z : Subgroup A}

omit [Finite K] [Finite A] in
theorem Hyp.comm_mem (h : Hyp ρ V Z) {v : K} (hv : v ∈ (V : Subgroup K)) (hv1 : v ≠ 1) (a : A) :
    ρ v a * a⁻¹ ∈ Z := b1_comm_mem h hv hv1 a

theorem Hyp.stab_iff (h : Hyp ρ V Z) (k : K) :
    (∀ a ∈ Z, ρ k a ∈ Z) ↔ k ∈ normalizer ((V : Subgroup K) : Set K) :=
  ⟨b1_stab_imp h, b1_imp_stab h⟩

theorem Hyp.not_normal (h : Hyp ρ V Z) : ¬ (V : Subgroup K).Normal := by
  intro hn
  apply h.notinv
  intro k a ha
  refine (h.stab_iff k).2 ?_ a ha
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top k

omit [Finite A] in
theorem Hyp.conj (h : Hyp ρ V Z) (k : K) :
    Hyp ρ (k • V) (Z.map (ρ k).toMonoidHom) := b1_conj h k

theorem Hyp.ti (h : Hyp ρ V Z) {k : K} (hk : k ∉ normalizer ((V : Subgroup K) : Set K)) :
    ∀ x ∈ (V : Subgroup K), x ∈ (k • V : Sylow 2 K) → x = 1 := by
  intro x hxV hxk
  by_contra hx1
  apply hk
  rw [← h.stab_iff k]
  intro a ha
  have hb : ρ k a ∈ Z.map (ρ k).toMonoidHom := Subgroup.mem_map_of_mem _ ha
  have h1 : ρ x (ρ k a) = ρ k a := ((h.conj k).fix x hxk hx1 _).2 hb
  exact (h.fix x hxV hx1 _).1 h1

end Basic

end CFSG.OddStandard.ThmC.O2.A8

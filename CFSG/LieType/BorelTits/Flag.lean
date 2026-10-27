module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type w} [Group H] (ρ : H →* Module.End K V)

@[expose] def flagStab (F : ℕ → Submodule K V) : Subgroup H where
  carrier := {h | ∀ k, ∀ v ∈ F k, ρ h v ∈ F k ∧ ρ h⁻¹ v ∈ F k}
  one_mem' := by
    intro k v hv
    simpa using hv
  mul_mem' := by
    intro g h hg hh k v hv
    refine ⟨?_, ?_⟩
    · rw [map_mul, Module.End.mul_apply]
      exact (hg k _ (hh k v hv).1).1
    · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
      exact (hh k _ (hg k v hv).2).2
  inv_mem' := by
    intro h hh k v hv
    refine ⟨(hh k v hv).2, ?_⟩
    rw [inv_inv]
    exact (hh k v hv).1

theorem mem_flagStab {F : ℕ → Submodule K V} {h : H} :
    h ∈ flagStab ρ F ↔ ∀ k, ∀ v ∈ F k, ρ h v ∈ F k ∧ ρ h⁻¹ v ∈ F k :=
  Iff.rfl

theorem flagStab_apply_mem {F : ℕ → Submodule K V} {h : H} (hh : h ∈ flagStab ρ F) {k : ℕ}
    {v : V} (hv : v ∈ F k) : ρ h v ∈ F k :=
  (hh k v hv).1

@[expose] def flagKernel (F : ℕ → Submodule K V) : Subgroup H where
  carrier := {h | h ∈ flagStab ρ F ∧ ∀ k, ∀ v ∈ F (k + 1), ρ h v - v ∈ F k}
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    intro k v _
    simp
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨mul_mem hg hh, ?_⟩
    intro k v hv
    have h1 : ρ h v ∈ F (k + 1) := flagStab_apply_mem ρ hh hv
    have : ρ (g * h) v - v = (ρ g (ρ h v) - ρ h v) + (ρ h v - v) := by
      rw [map_mul, Module.End.mul_apply]; abel
    rw [this]
    exact add_mem (hg' k _ h1) (hh' k v hv)
  inv_mem' := by
    rintro h ⟨hh, hh'⟩
    refine ⟨inv_mem hh, ?_⟩
    intro k v hv
    have hw : ρ h⁻¹ v ∈ F (k + 1) := (hh (k + 1) v hv).2
    have key := hh' k _ hw
    have : ρ h (ρ h⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [this] at key
    have := neg_mem key
    simpa using this

theorem flagKernel_le_flagStab (F : ℕ → Submodule K V) : flagKernel ρ F ≤ flagStab ρ F :=
  fun _ h => h.1

theorem mem_flagKernel {F : ℕ → Submodule K V} {h : H} :
    h ∈ flagKernel ρ F ↔ h ∈ flagStab ρ F ∧ ∀ k, ∀ v ∈ F (k + 1), ρ h v - v ∈ F k :=
  Iff.rfl

theorem flagStab_le_normalizer_flagKernel (F : ℕ → Submodule K V) :
    flagStab ρ F ≤ Subgroup.normalizer (flagKernel ρ F : Set H) := by
  have key : ∀ s ∈ flagStab ρ F, ∀ h ∈ flagKernel ρ F, s * h * s⁻¹ ∈ flagKernel ρ F := by
    intro s hs h hh
    refine ⟨mul_mem (mul_mem hs hh.1) (inv_mem hs), ?_⟩
    intro k v hv
    have hw : ρ s⁻¹ v ∈ F (k + 1) := (hs (k + 1) v hv).2
    have hin := hh.2 k _ hw
    have hs' : ρ s (ρ h (ρ s⁻¹ v) - ρ s⁻¹ v) ∈ F k := flagStab_apply_mem ρ hs hin
    have : ρ (s * h * s⁻¹) v - v = ρ s (ρ h (ρ s⁻¹ v) - ρ s⁻¹ v) := by
      rw [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (ρ s) (ρ s⁻¹), ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    rw [this]
    exact hs'
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key s hs h
  · intro hconj
    have := key s⁻¹ (inv_mem hs) _ hconj
    simpa [mul_assoc] using this

theorem pow_sub_one_mem {F : ℕ → Submodule K V} {h : H} (hh : h ∈ flagKernel ρ F) :
    ∀ i j : ℕ, ∀ v ∈ F (j + i), ((ρ h - 1) ^ i) v ∈ F j := by
  intro i
  induction i with
  | zero => intro j v hv; simpa using hv
  | succ i ih =>
    intro j v hv
    rw [pow_succ, Module.End.mul_apply]
    apply ih j
    have := hh.2 (j + i) v (by simpa [Nat.add_assoc] using hv)
    simpa using this

theorem isPGroup_flagKernel (p : ℕ) [Fact p.Prime] [CharP K p] (hρ : Function.Injective ρ)
    {F : ℕ → Submodule K V} (h0 : F 0 = ⊥) {m : ℕ} (hm : F m = ⊤) :
    IsPGroup p (flagKernel ρ F) := by
  intro x
  obtain ⟨e, he⟩ : ∃ e : ℕ, m ≤ p ^ e := ⟨m, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le⟩
  refine ⟨e, ?_⟩
  apply Subtype.ext
  apply hρ
  have hnil : (ρ x - 1) ^ m = 0 := by
    ext v
    have := pow_sub_one_mem ρ x.2 m 0 v (by simp [hm])
    rw [h0, Submodule.mem_bot] at this
    simpa using this
  have hnil' : (ρ x - 1) ^ (p ^ e) = 0 := by
    rw [← Nat.sub_add_cancel he, pow_add, hnil, mul_zero]
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Subsingleton.elim _ _
  have hinj : Function.Injective (algebraMap K (Module.End K V)) := by
    intro a b hab
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have := congrArg (fun f : Module.End K V => f v) hab
    simp only [Module.algebraMap_end_apply] at this
    exact smul_left_injective K hv this
  have : CharP (Module.End K V) p := charP_of_injective_algebraMap hinj p
  have hcomm : Commute (ρ x - 1) 1 := Commute.one_right _
  have := add_pow_char_pow_of_commute p e hcomm
  rw [sub_add_cancel, hnil', one_pow, zero_add] at this
  rw [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one, this]

theorem flagKernel_le_pCoreOf (p : ℕ) [Fact p.Prime] [CharP K p] (hρ : Function.Injective ρ)
    {F : ℕ → Submodule K V} (h0 : F 0 = ⊥) {m : ℕ} (hm : F m = ⊤) :
    flagKernel ρ F ≤ pCoreOf p (flagStab ρ F) :=
  le_pCoreOf_of_le_normalizer p (flagKernel_le_flagStab ρ F)
    (flagStab_le_normalizer_flagKernel ρ F) (isPGroup_flagKernel ρ p hρ h0 hm)

theorem holds_of_flags [Finite H] (p : ℕ) [Fact p.Prime] [CharP K p] (hρ : Function.Injective ρ)
    (𝔉 : Subgroup H → ℕ → Submodule K V)
    (h0 : ∀ R : Subgroup H, R ≠ ⊥ → IsPGroup p R → 𝔉 R 0 = ⊥)
    (htop : ∀ R : Subgroup H, R ≠ ⊥ → IsPGroup p R → ∃ m, 𝔉 R m = ⊤)
    (hnorm : ∀ R : Subgroup H, R ≠ ⊥ → IsPGroup p R →
      Subgroup.normalizer (R : Set H) ≤ flagStab ρ (𝔉 R))
    (hker : ∀ R : Subgroup H, R ≠ ⊥ → IsPGroup p R → R ≤ flagKernel ρ (𝔉 R))
    (hproper : ∀ R : Subgroup H, R ≠ ⊥ → IsPGroup p R → flagStab ρ (𝔉 R) ≠ ⊤)
    (hborel : ∀ R : Subgroup H, R ≠ ⊥ → IsPGroup p R →
      ∃ S : Sylow p H, Subgroup.normalizer ((S : Subgroup H) : Set H) ≤ flagStab ρ (𝔉 R)) :
    Holds H p := by
  intro U hU hUp
  set R := pCoreOf p (Subgroup.normalizer (U : Set H)) with hRdef
  have hUR : U ≤ R := le_pCoreOf_normalizer p U hUp
  have hR : R ≠ ⊥ := fun h => hU (le_bot_iff.mp (h ▸ hUR))
  have hRp : IsPGroup p R := pCoreOf_isPGroup p _
  obtain ⟨S, hS⟩ := hborel R hR hRp
  obtain ⟨m, hm⟩ := htop R hR hRp
  refine conclusion_of_core p U hUp S (flagStab ρ (𝔉 R)) (hproper R hR hRp) ?_ ?_ hS
  · exact (le_normalizer_pCoreOf p _).trans (hnorm R hR hRp)
  · exact (hker R hR hRp).trans (flagKernel_le_pCoreOf ρ p hρ (h0 R hR hRp) hm)

@[expose] def fixFlag (R : Subgroup H) : ℕ → Submodule K V
  | 0 => ⊥
  | k + 1 =>
    { carrier := {v | ∀ g ∈ R, ρ g v - v ∈ fixFlag R k}
      add_mem' := by
        intro a b ha hb g hg
        have := add_mem (ha g hg) (hb g hg)
        rw [map_add]
        convert this using 1
        abel
      zero_mem' := by
        intro g _
        simp
      smul_mem' := by
        intro c a ha g hg
        have := Submodule.smul_mem _ c (ha g hg)
        rw [map_smul, ← smul_sub]
        exact this }

@[simp] theorem fixFlag_zero (R : Subgroup H) : fixFlag ρ R 0 = ⊥ := rfl

theorem mem_fixFlag_succ {R : Subgroup H} {k : ℕ} {v : V} :
    v ∈ fixFlag ρ R (k + 1) ↔ ∀ g ∈ R, ρ g v - v ∈ fixFlag ρ R k :=
  Iff.rfl

theorem fixFlag_le_succ (R : Subgroup H) : ∀ k, fixFlag ρ R k ≤ fixFlag ρ R (k + 1) := by
  intro k
  induction k with
  | zero => intro v hv; simp [fixFlag] at hv; subst hv; intro g _; simp
  | succ k ih =>
    intro v hv g hg
    exact ih (hv g hg)

theorem fixFlag_mono (R : Subgroup H) : Monotone (fixFlag ρ R) :=
  monotone_nat_of_le_succ (fixFlag_le_succ ρ R)

theorem normalizer_le_flagStab_fixFlag (R : Subgroup H) :
    Subgroup.normalizer (R : Set H) ≤ flagStab ρ (fixFlag ρ R) := by
  have key : ∀ k, ∀ h ∈ Subgroup.normalizer (R : Set H), ∀ v ∈ fixFlag ρ R k,
      ρ h v ∈ fixFlag ρ R k := by
    intro k
    induction k with
    | zero => intro h _ v hv; simp [fixFlag] at hv ⊢; simp [hv]
    | succ k ih =>
      intro h hh v hv g hg
      have hg' : h⁻¹ * g * h ∈ R := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hh) g).mp hg
        simpa using this
      have hin := hv _ hg'
      have := ih h hh _ hin
      convert this using 1
      simp only [map_sub, map_mul, Module.End.mul_apply]
      rw [← Module.End.mul_apply (ρ h) (ρ h⁻¹), ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
  intro h hh k v hv
  exact ⟨key k h hh v hv, key k h⁻¹ (inv_mem hh) v hv⟩

theorem le_flagKernel_fixFlag (R : Subgroup H) : R ≤ flagKernel ρ (fixFlag ρ R) := by
  intro g hg
  refine ⟨(normalizer_le_flagStab_fixFlag ρ R) (Subgroup.le_normalizer hg), ?_⟩
  intro k v hv
  exact hv g hg

theorem exists_fixed_ne_zero [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p] (R : Subgroup H)
    (hR : IsPGroup p R) [Nontrivial V] :
    ∃ v : V, v ≠ 0 ∧ ∀ g ∈ R, ρ g v = v := by
  classical
  let : MulAction R V := MulAction.compHom V (ρ.comp R.subtype)
  have hsmul : ∀ (g : R) (v : V), g • v = ρ g v := fun _ _ => rfl
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hKfin : Finite K :=
    Finite.of_injective (fun c : K => c • v₀) (smul_left_injective K hv₀)
  have hdvd : p ∣ Nat.card V := by
    let := Fintype.ofFinite K
    let := Fintype.ofFinite V
    obtain ⟨n, -, hn⟩ := FiniteField.card K p
    have hpos : 0 < Module.finrank K V := Module.finrank_pos
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), hn]
    refine Dvd.dvd.pow ?_ hpos.ne'
    exact dvd_pow_self p n.pos.ne'
  have hmod := hR.card_modEq_card_fixedPoints V
  have hdvd' : p ∣ Nat.card (MulAction.fixedPoints R V) :=
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))
  have hzero : (0 : V) ∈ MulAction.fixedPoints R V := by
    intro g
    rw [hsmul, map_zero]
  have hpos : 0 < Nat.card (MulAction.fixedPoints R V) := by
    have : Nonempty (MulAction.fixedPoints R V) := ⟨⟨0, hzero⟩⟩
    exact Nat.card_pos
  have hone : 1 < Nat.card (MulAction.fixedPoints R V) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hdvd')
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := (Finite.one_lt_card_iff_nontrivial.mp hone).exists_pair_ne
  have hab' : a ≠ b := fun h => hab (Subtype.ext h)
  by_cases ha0 : a = 0
  · refine ⟨b, fun hb0 => hab' (ha0.trans hb0.symm), fun g hg => ?_⟩
    have := hb ⟨g, hg⟩
    rwa [hsmul] at this
  · refine ⟨a, ha0, fun g hg => ?_⟩
    have := ha ⟨g, hg⟩
    rwa [hsmul] at this

@[expose] def quotRep (R : Subgroup H) (W : Submodule K V)
    (hW : ∀ g ∈ R, ∀ v ∈ W, ρ g v ∈ W) : R →* Module.End K (V ⧸ W) where
  toFun g := W.mapQ W (ρ g) (fun v hv => hW g g.2 v hv)
  map_one' := by
    apply Submodule.linearMap_qext
    ext v
    simp
  map_mul' g h := by
    apply Submodule.linearMap_qext
    ext v
    simp

theorem quotRep_mk (R : Subgroup H) (W : Submodule K V) (hW : ∀ g ∈ R, ∀ v ∈ W, ρ g v ∈ W)
    (g : R) (v : V) :
    quotRep ρ R W hW g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) := rfl

theorem exists_fixFlag_eq_top [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p] (R : Subgroup H)
    (hR : IsPGroup p R) : ∃ m, fixFlag ρ R m = ⊤ := by
  classical
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian K V)
    ⟨fixFlag ρ R, fixFlag_mono ρ R⟩
  refine ⟨n, ?_⟩
  have hstab : fixFlag ρ R (n + 1) = fixFlag ρ R n := (hn (n + 1) (Nat.le_succ n)).symm
  by_contra hne
  set W := fixFlag ρ R n with hWdef
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ W := by
    by_contra h
    exact hne (eq_top_iff.mpr fun v _ => by
      by_contra hv
      exact h ⟨v, hv⟩)
  have hW : ∀ g ∈ R, ∀ v ∈ W, ρ g v ∈ W := fun g hg v hv =>
    flagStab_apply_mem ρ ((normalizer_le_flagStab_fixFlag ρ R) (Subgroup.le_normalizer hg)) hv
  have hnt : Nontrivial (V ⧸ W) := by
    refine ⟨⟨Submodule.Quotient.mk w, 0, ?_⟩⟩
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective W)
  have hRp : IsPGroup p (⊤ : Subgroup R) := hR.of_equiv Subgroup.topEquiv.symm
  obtain ⟨x, hx0, hx⟩ := exists_fixed_ne_zero (quotRep ρ R W hW) p ⊤ hRp
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W x
  apply hx0
  rw [Submodule.Quotient.mk_eq_zero]
  rw [← hstab]
  intro g hg
  have := hx ⟨g, hg⟩ (Subgroup.mem_top _)
  rw [quotRep_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero] at this
  exact this

end CFSG.LieType.BorelTits

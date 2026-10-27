module

public import CFSG.LieType.BorelTits.Flag

public section

namespace CFSG.LieType.BorelTits

universe u v w

structure ReflForm (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V] where
  σ : K ≃+* K
  β : V → V → K
  add_left : ∀ u u' v, β (u + u') v = β u v + β u' v
  smul_left : ∀ (c : K) u v, β (c • u) v = σ c * β u v
  add_right : ∀ u v v', β u (v + v') = β u v + β u v'
  smul_right : ∀ (c : K) u v, β u (c • v) = c * β u v
  refl : ∀ u v, β u v = 0 → β v u = 0
  nondeg : ∀ u, (∀ v, β u v = 0) → u = 0

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

namespace ReflForm

variable (F : ReflForm K V)

@[expose] def perp (W : Submodule K V) : Submodule K V where
  carrier := {v | ∀ w ∈ W, F.β w v = 0}
  add_mem' := by
    intro a b ha hb w hw
    rw [F.add_right, ha w hw, hb w hw, add_zero]
  zero_mem' := by
    intro w _
    have := F.smul_right 0 w 0
    rwa [zero_smul, zero_mul] at this
  smul_mem' := by
    intro c a ha w hw
    rw [F.smul_right, ha w hw, mul_zero]

theorem mem_perp {W : Submodule K V} {v : V} : v ∈ F.perp W ↔ ∀ w ∈ W, F.β w v = 0 :=
  Iff.rfl

theorem β_zero_right (u : V) : F.β u 0 = 0 := by
  have := F.smul_right 0 u 0
  rwa [zero_smul, zero_mul] at this

theorem β_zero_left (v : V) : F.β 0 v = 0 := by
  have := F.smul_left 0 0 v
  rwa [zero_smul, map_zero, zero_mul] at this

theorem β_sub_right (u v v' : V) : F.β u (v - v') = F.β u v - F.β u v' := by
  have h := F.add_right u (v - v') v'
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem β_sub_left (u u' v : V) : F.β (u - u') v = F.β u v - F.β u' v := by
  have h := F.add_left (u - u') u' v
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem perp_antitone {W W' : Submodule K V} (h : W ≤ W') : F.perp W' ≤ F.perp W :=
  fun _ hv w hw => hv w (h hw)

@[simp] theorem perp_bot : F.perp ⊥ = ⊤ := by
  ext v
  simp only [Submodule.mem_top, iff_true]
  intro w hw
  rw [Submodule.mem_bot] at hw
  rw [hw, F.β_zero_left]

@[simp] theorem perp_top : F.perp ⊤ = ⊥ := by
  ext v
  simp only [Submodule.mem_bot]
  constructor
  · intro hv
    exact F.nondeg v fun w => F.refl _ _ (hv w Submodule.mem_top)
  · rintro rfl
    exact (F.perp ⊤).zero_mem

theorem le_perp_perp (W : Submodule K V) : W ≤ F.perp (F.perp W) :=
  fun w hw _ hv => F.refl _ _ (hv w hw)

theorem perp_sup (W W' : Submodule K V) : F.perp (W ⊔ W') = F.perp W ⊓ F.perp W' := by
  refine le_antisymm (le_inf (F.perp_antitone le_sup_left) (F.perp_antitone le_sup_right)) ?_
  rintro v ⟨hW, hW'⟩ _ hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  rw [F.add_left, hW a ha, hW' b hb, add_zero]

theorem mem_perp_span_singleton {u v : V} : v ∈ F.perp (K ∙ u) ↔ F.β u v = 0 := by
  refine ⟨fun h => h u (Submodule.mem_span_singleton_self u), fun h w hw => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [F.smul_left, h, mul_zero]

@[expose] def toDual : V →ₛₗ[(F.σ : K →+* K)] Module.Dual K V where
  toFun u :=
    { toFun := F.β u
      map_add' := F.add_right u
      map_smul' := fun c v => F.smul_right c u v }
  map_add' u u' := LinearMap.ext (F.add_left u u')
  map_smul' c u := LinearMap.ext (F.smul_left c u)

@[simp] theorem toDual_apply (u v : V) : F.toDual u v = F.β u v :=
  rfl

theorem toDual_injective : Function.Injective F.toDual := by
  intro u u' h
  refine sub_eq_zero.mp (F.nondeg _ fun v => ?_)
  rw [F.β_sub_left, ← F.toDual_apply, ← F.toDual_apply, h, sub_self]

theorem perp_eq_dualCoannihilator (W : Submodule K V) :
    F.perp W = (W.map F.toDual).dualCoannihilator := by
  ext v
  simp [mem_perp, Submodule.mem_dualCoannihilator]

theorem finrank_map_toDual (W : Submodule K V) :
    Module.finrank K (W.map F.toDual) = Module.finrank K W := by
  let j : W ≃+ W.map F.toDual := AddEquiv.ofBijective (F.toDual.submoduleMap W)
    ⟨fun a b hab => Subtype.ext (F.toDual_injective (congrArg Subtype.val hab)),
      fun ⟨_, w, hw, hx⟩ => ⟨⟨w, hw⟩, Subtype.ext hx⟩⟩
  have h := lift_rank_eq_of_equiv_equiv (F.σ : K → K) j F.σ.bijective fun c w =>
    (F.toDual.submoduleMap W).map_smulₛₗ c w
  have h' := congrArg Cardinal.toNat h
  simp only [Cardinal.toNat_lift] at h'
  exact h'.symm

theorem finrank_perp [FiniteDimensional K V] (W : Submodule K V) :
    Module.finrank K (F.perp W) + Module.finrank K W = Module.finrank K V := by
  rw [F.perp_eq_dualCoannihilator, ← F.finrank_map_toDual W, add_comm]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq _

theorem perp_perp [FiniteDimensional K V] (W : Submodule K V) : F.perp (F.perp W) = W := by
  have h1 := F.finrank_perp W
  have h2 := F.finrank_perp (F.perp W)
  exact (Submodule.eq_of_le_of_finrank_eq (F.le_perp_perp W) (by omega)).symm

@[expose] def IsTotallyIsotropic (W : Submodule K V) : Prop :=
  W ≤ F.perp W

variable {F}

theorem IsTotallyIsotropic.mono {W W' : Submodule K V} (hW : F.IsTotallyIsotropic W)
    (h : W' ≤ W) : F.IsTotallyIsotropic W' :=
  h.trans (hW.trans (F.perp_antitone h))

theorem IsTotallyIsotropic.sup_span {W : Submodule K V} (hW : F.IsTotallyIsotropic W) {v : V}
    (hv : v ∈ F.perp W) (hvv : F.β v v = 0) : F.IsTotallyIsotropic (W ⊔ K ∙ v) := by
  have hWv : W ≤ F.perp (K ∙ v) := fun a ha =>
    F.mem_perp_span_singleton.mpr (F.refl _ _ (hv a ha))
  have hvv' : K ∙ v ≤ F.perp (K ∙ v) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (F.mem_perp_span_singleton.mpr hvv)
  have hvW : K ∙ v ≤ F.perp W := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
  rw [IsTotallyIsotropic, perp_sup]
  exact sup_le (le_inf hW hWv) (le_inf hvW hvv')

end ReflForm

variable {H : Type w} [Group H] (F : ReflForm K V) (ρ : H →* Module.End K V)

@[expose] def IsIsometric : Prop :=
  ∀ h u v, F.β (ρ h u) (ρ h v) = F.β u v

theorem IsIsometric.apply_mem_perp {F : ReflForm K V} {ρ : H →* Module.End K V}
    (hρ : IsIsometric F ρ) (h : H) {W : Submodule K V} {v : V} (hv : v ∈ F.perp W) :
    ρ h v ∈ F.perp (W.map (ρ h)) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [hρ]
  exact hv w hw

theorem rep_apply_inv_apply (h : H) (v : V) : ρ h (ρ h⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem IsIsometric.apply_mem_perp_of_forall {F : ReflForm K V} {ρ : H →* Module.End K V}
    (hρ : IsIsometric F ρ) {h : H} {W : Submodule K V} (hW : ∀ w ∈ W, ρ h⁻¹ w ∈ W) {v : V}
    (hv : v ∈ F.perp W) : ρ h v ∈ F.perp W := by
  intro w hw
  rw [← rep_apply_inv_apply ρ h w, hρ]
  exact hv _ (hW w hw)

theorem exists_mem_notMem_forall_sub_mem [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (R : Subgroup H) (hR : IsPGroup p R) {A B : Submodule K V} (hAB : A < B)
    (hA : ∀ g ∈ R, ∀ v ∈ A, ρ g v ∈ A) (hB : ∀ g ∈ R, ∀ v ∈ B, ρ g v ∈ B) :
    ∃ v ∈ B, v ∉ A ∧ ∀ g ∈ R, ρ g v - v ∈ A := by
  set A' : Submodule K B := A.comap B.subtype
  let ρ' : R →* Module.End K (B ⧸ A') :=
    { toFun := fun g => A'.mapQ A' ((ρ g).restrict fun v hv => hB g g.2 v hv)
        fun v hv => hA g g.2 v hv
      map_one' := by
        apply Submodule.linearMap_qext
        ext v
        simp [LinearMap.restrict_apply]
      map_mul' := fun g h => by
        apply Submodule.linearMap_qext
        ext v
        simp only [Subgroup.coe_mul, map_mul]
        rfl }
  have hρ' : ∀ (g : R) (v : B), ρ' g (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨ρ g v, hB g g.2 v v.2⟩ := fun _ _ => rfl
  obtain ⟨b, hbB, hbA⟩ := IsConcreteLE.not_le_iff_exists.mp hAB.not_ge
  have : Nontrivial (B ⧸ A') := ⟨⟨Submodule.Quotient.mk ⟨b, hbB⟩, 0, by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hbA⟩⟩
  have : Finite (B ⧸ A') := Finite.of_surjective _ (Submodule.Quotient.mk_surjective A')
  obtain ⟨x, hx0, hx⟩ := exists_fixed_ne_zero ρ' p ⊤ (hR.of_equiv Subgroup.topEquiv.symm)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective A' x
  refine ⟨v, v.2, fun hv => hx0 ((Submodule.Quotient.mk_eq_zero A').mpr hv), fun g hg => ?_⟩
  have := hx ⟨g, hg⟩ (Subgroup.mem_top _)
  rw [hρ', ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero] at this
  exact this

@[expose] def relFix (W : Submodule K V) (R : Subgroup H) : Submodule K V where
  carrier := {v | v ∈ F.perp W ∧ ∀ g ∈ R, ρ g v - v ∈ W}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, fun g hg => ?_⟩
    have := add_mem (ha' g hg) (hb' g hg)
    rw [map_add]
    convert this using 1
    abel
  zero_mem' := ⟨Submodule.zero_mem _, fun g _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Submodule.smul_mem _ c ha, fun g hg => ?_⟩
    have := Submodule.smul_mem _ c (ha' g hg)
    rw [map_smul, ← smul_sub]
    exact this

theorem mem_relFix {W : Submodule K V} {R : Subgroup H} {v : V} :
    v ∈ relFix F ρ W R ↔ v ∈ F.perp W ∧ ∀ g ∈ R, ρ g v - v ∈ W :=
  Iff.rfl

theorem relFix_le_perp (W : Submodule K V) (R : Subgroup H) : relFix F ρ W R ≤ F.perp W :=
  fun _ hv => hv.1

theorem le_perp_relFix (W : Submodule K V) (R : Subgroup H) : W ≤ F.perp (relFix F ρ W R) :=
  (F.le_perp_perp W).trans (F.perp_antitone (relFix_le_perp F ρ W R))

theorem le_relFix {W : Submodule K V} {R : Subgroup H} (hW : F.IsTotallyIsotropic W)
    (hWR : ∀ g ∈ R, ∀ v ∈ W, ρ g v ∈ W) : W ≤ relFix F ρ W R :=
  fun v hv => ⟨hW hv, fun g hg => sub_mem (hWR g hg v hv) hv⟩

theorem apply_mem_relFix {W : Submodule K V} {R : Subgroup H} (hW : F.IsTotallyIsotropic W)
    (hWR : ∀ g ∈ R, ∀ v ∈ W, ρ g v ∈ W) {g : H} (hg : g ∈ R) {v : V}
    (hv : v ∈ relFix F ρ W R) : ρ g v ∈ relFix F ρ W R := by
  simpa using add_mem (le_relFix F ρ hW hWR (hv.2 g hg)) hv

@[expose] def isoNext (R : Subgroup H) (W : Submodule K V) : Submodule K V :=
  relFix F ρ W R ⊓ F.perp (relFix F ρ W R)

theorem isoNext_isTotallyIsotropic (R : Subgroup H) (W : Submodule K V) :
    F.IsTotallyIsotropic (isoNext F ρ R W) :=
  inf_le_right.trans (F.perp_antitone inf_le_left)

theorem le_isoNext {R : Subgroup H} {W : Submodule K V} (hW : F.IsTotallyIsotropic W)
    (hWR : ∀ g ∈ R, ∀ v ∈ W, ρ g v ∈ W) : W ≤ isoNext F ρ R W :=
  le_inf (le_relFix F ρ hW hWR) (le_perp_relFix F ρ W R)

theorem apply_mem_isoNext {R : Subgroup H} {W : Submodule K V} (hW : F.IsTotallyIsotropic W)
    (hWR : ∀ g ∈ R, ∀ v ∈ W, ρ g v ∈ W) {g : H} (hg : g ∈ R) {v : V}
    (hv : v ∈ isoNext F ρ R W) : ρ g v ∈ isoNext F ρ R W := by
  simpa using add_mem (le_isoNext F ρ hW hWR (hv.1.2 g hg)) hv

@[expose] def isoSeq (R : Subgroup H) : ℕ → Submodule K V
  | 0 => ⊥
  | k + 1 => isoNext F ρ R (isoSeq R k)

@[simp] theorem isoSeq_zero (R : Subgroup H) : isoSeq F ρ R 0 = ⊥ := rfl

theorem isoSeq_succ (R : Subgroup H) (k : ℕ) :
    isoSeq F ρ R (k + 1) = isoNext F ρ R (isoSeq F ρ R k) := rfl

theorem isoSeq_isTotallyIsotropic (R : Subgroup H) (k : ℕ) :
    F.IsTotallyIsotropic (isoSeq F ρ R k) := by
  cases k with
  | zero => exact bot_le
  | succ k => exact isoNext_isTotallyIsotropic F ρ R _

theorem apply_mem_isoSeq_of_mem (R : Subgroup H) (k : ℕ) {g : H} (hg : g ∈ R) {v : V}
    (hv : v ∈ isoSeq F ρ R k) : ρ g v ∈ isoSeq F ρ R k := by
  induction k generalizing g v with
  | zero =>
    rw [isoSeq_zero, Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  | succ k ih =>
    exact apply_mem_isoNext F ρ (isoSeq_isTotallyIsotropic F ρ R k)
      (fun _ hg' _ hw => ih hg' hw) hg hv

theorem isoSeq_le_succ (R : Subgroup H) (k : ℕ) : isoSeq F ρ R k ≤ isoSeq F ρ R (k + 1) :=
  le_isoNext F ρ (isoSeq_isTotallyIsotropic F ρ R k) fun _ hg _ hv =>
    apply_mem_isoSeq_of_mem F ρ R k hg hv

theorem isoSeq_mono (R : Subgroup H) : Monotone (isoSeq F ρ R) :=
  monotone_nat_of_le_succ (isoSeq_le_succ F ρ R)

theorem isoSeq_triv (R : Subgroup H) (k : ℕ) {g : H} (hg : g ∈ R) {v : V}
    (hv : v ∈ isoSeq F ρ R (k + 1)) : ρ g v - v ∈ isoSeq F ρ R k :=
  (hv.1).2 g hg

theorem apply_mem_isoSeq (hρ : IsIsometric F ρ) (R : Subgroup H) (k : ℕ) {h : H}
    (hh : h ∈ Subgroup.normalizer (R : Set H)) {v : V} (hv : v ∈ isoSeq F ρ R k) :
    ρ h v ∈ isoSeq F ρ R k := by
  induction k generalizing h v with
  | zero =>
    rw [isoSeq_zero, Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  | succ k ih =>
    have hΦ : ∀ h ∈ Subgroup.normalizer (R : Set H), ∀ u ∈ relFix F ρ (isoSeq F ρ R k) R,
        ρ h u ∈ relFix F ρ (isoSeq F ρ R k) R := by
      intro h hh u hu
      refine ⟨hρ.apply_mem_perp_of_forall (fun w hw => ih (inv_mem hh) hw) hu.1, fun g hg => ?_⟩
      have hg' : h⁻¹ * g * h ∈ R := by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hh) g).mp hg
      have := ih hh (hu.2 _ hg')
      rwa [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        rep_apply_inv_apply] at this
    exact ⟨hΦ h hh v hv.1, hρ.apply_mem_perp_of_forall (fun w hw => hΦ _ (inv_mem hh) w hw) hv.2⟩

theorem isoSeq_eq_of_succ_eq (R : Subgroup H) {k : ℕ}
    (hk : isoSeq F ρ R (k + 1) = isoSeq F ρ R k) {j : ℕ} (hj : k ≤ j) :
    isoSeq F ρ R j = isoSeq F ρ R k := by
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j _ ih => rw [isoSeq_succ, ih, ← isoSeq_succ, hk]

theorem isoSeq_eq_of_le [FiniteDimensional K V] (R : Subgroup H) {j : ℕ}
    (hj : Module.finrank K V ≤ j) : isoSeq F ρ R j = isoSeq F ρ R (Module.finrank K V) := by
  have hlen : ∀ n, (∀ k < n, isoSeq F ρ R k < isoSeq F ρ R (k + 1)) →
      n ≤ Module.finrank K (isoSeq F ρ R n) := by
    intro n
    induction n with
    | zero => exact fun _ => Nat.zero_le _
    | succ n ih =>
      intro h
      have h1 := Submodule.finrank_lt_finrank_of_lt (h n n.lt_succ_self)
      have h2 := ih fun k hk => h k (hk.trans n.lt_succ_self)
      omega
  obtain ⟨k, hk, hkeq⟩ : ∃ k ≤ Module.finrank K V, isoSeq F ρ R (k + 1) = isoSeq F ρ R k := by
    by_contra! h
    have h1 := hlen (Module.finrank K V + 1) fun k hk =>
      lt_of_le_of_ne (isoSeq_le_succ F ρ R k) (h k (Nat.lt_succ_iff.mp hk)).symm
    have h2 := Submodule.finrank_le (isoSeq F ρ R (Module.finrank K V + 1))
    omega
  rw [isoSeq_eq_of_succ_eq F ρ R hkeq (hk.trans hj), isoSeq_eq_of_succ_eq F ρ R hkeq hk]

theorem isoSeq_middle_triv [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : IsIsometric F ρ) (R : Subgroup H) (hR : IsPGroup p R) {g : H} (hg : g ∈ R) {v : V}
    (hv : v ∈ F.perp (isoSeq F ρ R (Module.finrank K V))) :
    ρ g v - v ∈ isoSeq F ρ R (Module.finrank K V) := by
  set W := isoSeq F ρ R (Module.finrank K V)
  have hWiso : F.IsTotallyIsotropic W := isoSeq_isTotallyIsotropic F ρ R _
  have hWinv : ∀ g ∈ R, ∀ w ∈ W, ρ g w ∈ W := fun g hg w hw =>
    apply_mem_isoSeq_of_mem F ρ R _ hg hw
  have hstab : isoNext F ρ R W = W := isoSeq_eq_of_le F ρ R (Nat.le_succ _)
  have hΦ : F.perp (relFix F ρ W R) = W := by
    by_contra hne
    obtain ⟨u, hu, huW, hufix⟩ := exists_mem_notMem_forall_sub_mem ρ p R hR
      (lt_of_le_of_ne (le_perp_relFix F ρ W R) (Ne.symm hne)) hWinv fun g hg u hu =>
        hρ.apply_mem_perp_of_forall
          (fun w hw => apply_mem_relFix F ρ hWiso hWinv (inv_mem hg) hw) hu
    apply huW
    rw [← hstab]
    exact ⟨⟨F.perp_antitone (le_relFix F ρ hWiso hWinv) hu, hufix⟩, hu⟩
  have hvΦ : v ∈ relFix F ρ W R := by
    rw [← F.perp_perp (relFix F ρ W R), hΦ]
    exact hv
  exact hvΦ.2 g hg

theorem perp_isoSeq_triv (hρ : IsIsometric F ρ) (R : Subgroup H) (k : ℕ) {g : H} (hg : g ∈ R)
    {v : V} (hv : v ∈ F.perp (isoSeq F ρ R k)) :
    ρ g v - v ∈ F.perp (isoSeq F ρ R (k + 1)) := by
  intro w hw
  have h1 := hρ g (ρ g⁻¹ w) v
  rw [rep_apply_inv_apply] at h1
  rw [F.β_sub_right, h1, ← F.β_sub_left]
  exact hv _ (isoSeq_triv F ρ R k (inv_mem hg) hw)

theorem isoSeq_one_ne_bot [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) (R : Subgroup H) (hR : IsPGroup p R)
    (hne : R ≠ ⊥) : isoSeq F ρ R 1 ≠ ⊥ := by
  intro h1
  have hbot : isoSeq F ρ R (Module.finrank K V) = ⊥ :=
    isoSeq_eq_of_succ_eq F ρ R (k := 0) h1 (Nat.zero_le _)
  refine hne ((Subgroup.eq_bot_iff_forall R).mpr fun g hg => hinj ?_)
  ext v
  have := isoSeq_middle_triv F ρ p hρ R hR hg (v := v) (by rw [hbot, F.perp_bot]; trivial)
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
  rw [this, map_one, Module.End.one_apply]

@[expose] noncomputable def isoFlag (R : Subgroup H) (k : ℕ) : Submodule K V :=
  if k ≤ Module.finrank K V then isoSeq F ρ R k
  else if k ≤ 2 * Module.finrank K V + 1 then
    F.perp (isoSeq F ρ R (2 * Module.finrank K V + 1 - k))
  else ⊤

theorem isoFlag_zero (R : Subgroup H) : isoFlag F ρ R 0 = ⊥ := by
  simp [isoFlag]

theorem isoFlag_top [FiniteDimensional K V] (R : Subgroup H) :
    isoFlag F ρ R (2 * Module.finrank K V + 1) = ⊤ := by
  rw [isoFlag, ite_eq_right (by omega), ite_eq_left le_rfl, Nat.sub_self, isoSeq_zero, F.perp_bot]

theorem le_flagStab_isoFlag (hρ : IsIsometric F ρ) (R G : Subgroup H)
    (hG : ∀ h ∈ G, ∀ k, ∀ v ∈ isoSeq F ρ R k, ρ h v ∈ isoSeq F ρ R k) :
    G ≤ flagStab ρ (isoFlag F ρ R) := by
  have key : ∀ h ∈ G, ∀ k, ∀ v ∈ isoFlag F ρ R k, ρ h v ∈ isoFlag F ρ R k := by
    intro h hh k v hv
    unfold isoFlag at hv ⊢
    split_ifs at hv ⊢
    · exact hG h hh k v hv
    · exact hρ.apply_mem_perp_of_forall (fun w hw => hG _ (inv_mem hh) _ w hw) hv
    · exact Submodule.mem_top
  intro h hh k v hv
  exact ⟨key h hh k v hv, key h⁻¹ (inv_mem hh) k v hv⟩

theorem normalizer_le_flagStab_isoFlag [FiniteDimensional K V] (hρ : IsIsometric F ρ)
    (R : Subgroup H) : Subgroup.normalizer (R : Set H) ≤ flagStab ρ (isoFlag F ρ R) :=
  le_flagStab_isoFlag F ρ hρ R _ fun _ hh k _ hv => apply_mem_isoSeq F ρ hρ R k hh hv

theorem le_flagKernel_isoFlag [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : IsIsometric F ρ) (R : Subgroup H) (hR : IsPGroup p R) :
    R ≤ flagKernel ρ (isoFlag F ρ R) := by
  intro g hg
  refine ⟨normalizer_le_flagStab_isoFlag F ρ hρ R (Subgroup.le_normalizer hg), fun k v hv => ?_⟩
  rcases Nat.lt_or_ge k (Module.finrank K V) with hk | hk
  · rw [isoFlag, ite_eq_left (by omega)] at hv
    rw [isoFlag, ite_eq_left hk.le]
    exact isoSeq_triv F ρ R k hg hv
  rcases hk.lt_or_eq with hk | rfl
  · rw [isoFlag, ite_eq_right (by omega)] at hv ⊢
    by_cases hk2 : k + 1 ≤ 2 * Module.finrank K V + 1
    · rw [ite_eq_left hk2] at hv
      rw [ite_eq_left (by omega), show 2 * Module.finrank K V + 1 - k =
        2 * Module.finrank K V + 1 - (k + 1) + 1 by omega]
      exact perp_isoSeq_triv F ρ hρ R _ hg hv
    · by_cases hk3 : k ≤ 2 * Module.finrank K V + 1
      · rw [ite_eq_left hk3, show 2 * Module.finrank K V + 1 - k = 0 by omega, isoSeq_zero,
          F.perp_bot]
        trivial
      · rw [ite_eq_right hk3]
        trivial
  · rw [isoFlag, ite_eq_right (by omega), ite_eq_left (by omega),
      show 2 * Module.finrank K V + 1 - (Module.finrank K V + 1) = Module.finrank K V by omega]
      at hv
    rw [isoFlag, ite_eq_left le_rfl]
    exact isoSeq_middle_triv F ρ p hρ R hR hg hv

theorem holds_of_isoFlags [Finite H] [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ)
    (hproper : ∀ W : Submodule K V, W ≠ ⊥ → F.IsTotallyIsotropic W →
      ∃ h : H, ∃ w ∈ W, ρ h w ∉ W)
    (hborel : ∀ R : Subgroup H, R ≠ ⊥ → IsPGroup p R →
      ∃ S : Sylow p H, Subgroup.normalizer ((S : Subgroup H) : Set H) ≤
        flagStab ρ (isoFlag F ρ R)) :
    Holds H p := by
  refine holds_of_flags ρ p hinj (fun R => isoFlag F ρ R) (fun R _ _ => isoFlag_zero F ρ R)
    (fun R _ _ => ⟨_, isoFlag_top F ρ R⟩) (fun R _ _ => normalizer_le_flagStab_isoFlag F ρ hρ R)
    (fun R _ hR => le_flagKernel_isoFlag F ρ p hρ R hR) (fun R hR hRp htop => ?_) hborel
  have h1 := isoSeq_one_ne_bot F ρ p hρ hinj R hRp hR
  obtain ⟨h, w, hw, hhw⟩ := hproper _ h1 (isoSeq_isTotallyIsotropic F ρ R 1)
  have hd : 1 ≤ Module.finrank K V := by
    obtain ⟨x, -, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    have : Nontrivial V := ⟨⟨x, 0, hx0⟩⟩
    exact Module.finrank_pos
  have hflag : isoFlag F ρ R 1 = isoSeq F ρ R 1 := ite_eq_left hd
  refine hhw ?_
  rw [← hflag] at hw ⊢
  exact flagStab_apply_mem ρ (htop ▸ Subgroup.mem_top h) hw

theorem exists_sylow_normalizer_le_flagStab_of_isotropicChain [Finite H] [Finite V] (p : ℕ)
    [Fact p.Prime] [CharP K p] (hρ : IsIsometric F ρ) (X : ℕ → Submodule K V)
    (m m' : ℕ) (hm' : m' ≤ m) (hX0 : X 0 = ⊥) (hXmono : Monotone X)
    (hXiso : ∀ k, F.IsTotallyIsotropic (X k))
    (hXrank : ∀ k ≤ m, Module.finrank K (X k) = k) (hXstable : ∀ k, m ≤ k → X k = X m)
    (U' : Subgroup H) (hU'p : IsPGroup p U')
    (hstep : ∀ k < m', ∀ v ∈ F.perp (X k), (∀ g ∈ U', ρ g v - v ∈ X k) → v ∈ X (k + 1))
    (hmiddle : ∀ S : Subgroup H, IsPGroup p S → S ≤ flagStab ρ (fun _ => X m') →
      ∀ g ∈ S, ∀ v ∈ F.perp (X m'), ρ g v - v ∈ X m')
    (hrest : ∀ S : Sylow p H, (∀ k, isoSeq F ρ S k = X (min k m')) →
      ∀ k, m' < k → k ≤ m →
        Subgroup.normalizer ((S : Subgroup H) : Set H) ≤ flagStab ρ (fun _ => X k)) :
    ∃ S : Sylow p H, Subgroup.normalizer ((S : Subgroup H) : Set H) ≤ flagStab ρ X := by
  obtain ⟨S, hS⟩ := hU'p.exists_le_sylow
  refine ⟨S, ?_⟩
  have hseq : ∀ k, isoSeq F ρ S k = X (min k m') := by
    intro k
    induction k with
    | zero => rw [isoSeq_zero, Nat.zero_min, hX0]
    | succ k ih =>
      have hinv : ∀ g ∈ (S : Subgroup H), ∀ v ∈ X (min k m'), ρ g v ∈ X (min k m') := by
        intro g hg v hv
        rw [← ih] at hv ⊢
        exact apply_mem_isoSeq_of_mem F ρ S k hg hv
      rw [isoSeq_succ, ih]
      rcases Nat.lt_or_ge k m' with hk | hk
      · rw [min_eq_left hk.le] at hinv ⊢
        rw [min_eq_left hk]
        have hrk : Module.finrank K (X k) = k := hXrank k (by omega)
        have hrk' : Module.finrank K (X (k + 1)) = k + 1 := hXrank (k + 1) (by omega)
        have hlt : X k < X (k + 1) :=
          lt_of_le_of_ne (hXmono k.le_succ) fun h => by rw [h] at hrk; omega
        have hle : X (k + 1) ≤ F.perp (X k) :=
          (hXiso (k + 1)).trans (F.perp_antitone (hXmono k.le_succ))
        obtain ⟨u, hu, huX, hufix⟩ := exists_mem_notMem_forall_sub_mem ρ p S S.isPGroup'
          (hlt.trans_le hle) hinv fun g hg v hv =>
            hρ.apply_mem_perp_of_forall (fun w hw => hinv _ (inv_mem hg) w hw) hv
        have hΦle : relFix F ρ (X k) S ≤ X (k + 1) := fun v hv =>
          hstep k hk v hv.1 fun g hg => hv.2 g (hS hg)
        have hΦlt : X k < relFix F ρ (X k) S :=
          lt_of_le_of_ne (le_relFix F ρ (hXiso k) hinv) fun h => huX (h ▸ ⟨hu, hufix⟩)
        have hΦ : relFix F ρ (X k) S = X (k + 1) := by
          refine Submodule.eq_of_le_of_finrank_eq hΦle ?_
          have h1 := Submodule.finrank_lt_finrank_of_lt hΦlt
          have h2 := Submodule.finrank_mono hΦle
          omega
        rw [isoNext, hΦ]
        exact inf_eq_left.mpr (hXiso (k + 1))
      · rw [min_eq_right hk] at hinv ⊢
        rw [min_eq_right (hk.trans k.le_succ)]
        have hSstab : (S : Subgroup H) ≤ flagStab ρ (fun _ => X m') :=
          fun g hg _ v hv => ⟨hinv g hg v hv, hinv _ (inv_mem hg) v hv⟩
        have hΦ : relFix F ρ (X m') S = F.perp (X m') :=
          le_antisymm (relFix_le_perp F ρ _ _) fun v hv =>
            ⟨hv, fun g hg => hmiddle S S.isPGroup' hSstab g hg v hv⟩
        rw [isoNext, hΦ, F.perp_perp]
        exact inf_eq_right.mpr (hXiso m')
  have hNX' : ∀ h ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ k ≤ m, ∀ v ∈ X k,
      ρ h v ∈ X k := by
    intro h hh k hk v hv
    rcases le_or_gt k m' with hkm' | hkm'
    · have hXk : isoSeq F ρ S k = X k := by rw [hseq, min_eq_left hkm']
      rw [← hXk] at hv ⊢
      exact apply_mem_isoSeq F ρ hρ S k hh hv
    · exact flagStab_apply_mem ρ (hrest S hseq k hkm' hk hh) (k := 0) hv
  have hNX : ∀ h ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ k, ∀ v ∈ X k,
      ρ h v ∈ X k := by
    intro h hh k v hv
    rcases le_total k m with hk | hk
    · exact hNX' h hh k hk v hv
    · rw [hXstable k hk] at hv ⊢
      exact hNX' h hh m le_rfl v hv
  exact fun h hh k v hv => ⟨hNX h hh k v hv, hNX h⁻¹ (inv_mem hh) k v hv⟩

theorem exists_sylow_normalizer_le_of_isotropicChain [Finite H] [Finite V] (p : ℕ)
    [Fact p.Prime] [CharP K p] (hρ : IsIsometric F ρ) (R : Subgroup H) (X : ℕ → Submodule K V)
    (m m' : ℕ) (hm' : m' ≤ m) (hX0 : X 0 = ⊥) (hXmono : Monotone X)
    (hXiso : ∀ k, F.IsTotallyIsotropic (X k))
    (hXrank : ∀ k ≤ m, Module.finrank K (X k) = k) (hXstable : ∀ k, m ≤ k → X k = X m)
    (hrefine : ∀ j, ∃ k, isoSeq F ρ R j = X k)
    (U' : Subgroup H) (hU'p : IsPGroup p U') (_hU'stab : U' ≤ flagStab ρ X)
    (hstep : ∀ k < m', ∀ v ∈ F.perp (X k), (∀ g ∈ U', ρ g v - v ∈ X k) → v ∈ X (k + 1))
    (hmiddle : ∀ S : Subgroup H, IsPGroup p S → S ≤ flagStab ρ (fun _ => X m') →
      ∀ g ∈ S, ∀ v ∈ F.perp (X m'), ρ g v - v ∈ X m')
    (hrest : ∀ S : Sylow p H, (∀ k, isoSeq F ρ S k = X (min k m')) →
      ∀ k, m' < k → k ≤ m →
        Subgroup.normalizer ((S : Subgroup H) : Set H) ≤ flagStab ρ (fun _ => X k)) :
    ∃ S : Sylow p H, Subgroup.normalizer ((S : Subgroup H) : Set H) ≤
      flagStab ρ (isoFlag F ρ R) := by
  obtain ⟨S, hS⟩ := exists_sylow_normalizer_le_flagStab_of_isotropicChain F ρ p hρ X m m' hm' hX0
    hXmono hXiso hXrank hXstable U' hU'p hstep hmiddle hrest
  refine ⟨S, le_flagStab_isoFlag F ρ hρ R _ fun h hh j v hv => ?_⟩
  obtain ⟨k, hk⟩ := hrefine j
  rw [hk] at hv ⊢
  exact flagStab_apply_mem ρ (hS hh) hv

theorem exists_finrank_chain_forall_exists_eq [FiniteDimensional K V] {G : ℕ → Submodule K V}
    (hG : Monotone G) {M : Submodule K V} (hGM : ∀ j, G j ≤ M) (hM : ∃ n, G n = M) :
    ∃ X : ℕ → Submodule K V, X 0 = ⊥ ∧ Monotone X ∧
      (∀ k ≤ Module.finrank K M, Module.finrank K (X k) = k) ∧
      (∀ k, Module.finrank K M ≤ k → X k = M) ∧ ∀ j, ∃ k, G j = X k := by
  classical
  have hnext : ∀ Y : Submodule K V, ∃ u ∈ M, ∀ h : ∃ k, ¬G k ≤ Y, u ∈ G (Nat.find h) ∧ u ∉ Y := by
    intro Y
    by_cases h : ∃ k, ¬G k ≤ Y
    · obtain ⟨u, hu, hu'⟩ := IsConcreteLE.not_le_iff_exists.mp (Nat.find_spec h)
      exact ⟨u, hGM _ hu, fun _ => ⟨hu, hu'⟩⟩
    · exact ⟨0, M.zero_mem, fun h' => absurd h' h⟩
  choose next hnextM hnext using hnext
  let X : ℕ → Submodule K V := fun i => (fun Y => Y ⊔ K ∙ next Y)^[i] ⊥
  have hXs : ∀ i, X (i + 1) = X i ⊔ K ∙ next (X i) := fun i =>
    Function.iterate_succ_apply' _ i ⊥
  have hmono : Monotone X := monotone_nat_of_le_succ fun i => (hXs i).symm ▸ le_sup_left
  have hXM : ∀ i, X i ≤ M := by
    intro i
    induction i with
    | zero => exact bot_le
    | succ i ih =>
      rw [hXs]
      exact sup_le ih ((Submodule.span_singleton_le_iff_mem _ _).mpr (hnextM _))
  have hstep : ∀ i k, ¬G k ≤ X i → X i ≤ G k → X (i + 1) ≤ G k := by
    intro i k hk hle
    rw [hXs]
    refine sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    exact hG (Nat.find_min' ⟨k, hk⟩ hk) (hnext (X i) ⟨k, hk⟩).1
  have hcomp : ∀ i k, G k ≤ X i ∨ X i ≤ G k := by
    intro i
    induction i with
    | zero => exact fun k => Or.inr bot_le
    | succ i ih =>
      intro k
      by_cases hk : G k ≤ X i
      · exact Or.inl (hk.trans (hmono (Nat.le_succ i)))
      · exact Or.inr (hstep i k hk ((ih k).resolve_left hk))
  obtain ⟨n, hn⟩ := hM
  have hrank : ∀ i ≤ Module.finrank K M, Module.finrank K (X i) = i := by
    intro i
    induction i with
    | zero => exact fun _ => finrank_bot K V
    | succ i ih =>
      intro hi
      have hXi := ih (by omega)
      have hne : ¬G n ≤ X i := fun hle => by
        rw [le_antisymm (hXM i) (hn ▸ hle)] at hXi
        omega
      have hu := (hnext (X i) ⟨n, hne⟩).2
      have hu0 : next (X i) ≠ 0 := fun h0 => hu (h0 ▸ (X i).zero_mem)
      have hdisj : X i ⊓ K ∙ next (X i) = ⊥ :=
        ((Submodule.disjoint_span_singleton' hu0).mpr hu).eq_bot
      have := Submodule.finrank_sup_add_finrank_inf_eq (X i) (K ∙ next (X i))
      rw [hdisj, finrank_bot, finrank_span_singleton hu0, hXi, ← hXs] at this
      omega
  have htop : X (Module.finrank K M) = M :=
    Submodule.eq_of_le_of_finrank_eq (hXM _) (hrank _ le_rfl)
  refine ⟨X, rfl, hmono, hrank, fun k hk => le_antisymm (hXM k) (htop ▸ hmono hk), fun j => ?_⟩
  have hex : ∃ i, G j ≤ X i := ⟨_, htop.symm ▸ hGM j⟩
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i := ⟨_, rfl⟩
  have hle : G j ≤ X i := hi ▸ Nat.find_spec hex
  cases i with
  | zero => exact ⟨0, le_antisymm hle bot_le⟩
  | succ i =>
    have hnle : ¬G j ≤ X i := Nat.find_min hex (by omega)
    exact ⟨i + 1, le_antisymm hle (hstep i j hnle ((hcomp i j).resolve_left hnle))⟩

theorem exists_chain_refining_of_maximal [FiniteDimensional K V] {P : Submodule K V → Prop}
    (hP : ∀ {M M' : Submodule K V}, P M → M' ≤ M → P M') (W : ℕ → Submodule K V)
    (hW0 : W 0 = ⊥) (hWmono : Monotone W) (hWP : ∀ j, P (W j)) :
    ∃ (X : ℕ → Submodule K V) (m : ℕ), X 0 = ⊥ ∧ Monotone X ∧ (∀ k, P (X k)) ∧
      (∀ k ≤ m, Module.finrank K (X k) = k) ∧ (∀ k, m ≤ k → X k = X m) ∧
      (∀ j, ∃ k, W j = X k) ∧ ∀ M, X m ≤ M → P M → M ≤ X m := by
  classical
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian K V)
    ⟨W, hWmono⟩
  have hN' : ∀ j, N ≤ j → W j = W N := fun j hj => (hN j hj).symm
  obtain ⟨M, ⟨hWM, hMP⟩, hMmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian K V) {M | W N ≤ M ∧ P M} ⟨W N, le_rfl, hWP N⟩
  have hWle : ∀ j, W j ≤ M := fun j =>
    (le_total j N).elim (fun h => (hWmono h).trans hWM) fun h => (hN' j h).symm ▸ hWM
  let G : ℕ → Submodule K V := fun j => if j ≤ N then W j else M
  have hG : Monotone G := by
    intro i j hij
    simp only [G]
    split_ifs with hi hj hj
    · exact hWmono hij
    · exact hWle i
    · omega
    · exact le_rfl
  have hGM : ∀ j, G j ≤ M := fun j => by
    simp only [G]
    split_ifs
    exacts [hWle j, le_rfl]
  obtain ⟨X, hX0, hXmono, hXrank, hXtop, hXG⟩ :=
    exists_finrank_chain_forall_exists_eq hG hGM ⟨N + 1, ite_eq_right (by omega)⟩
  have hXm : X (Module.finrank K M) = M := hXtop _ le_rfl
  refine ⟨X, Module.finrank K M, hX0, hXmono, fun k => hP hMP ?_, hXrank,
    fun k hk => (hXtop k hk).trans hXm.symm, fun j => ?_, ?_⟩
  · exact (hXmono (le_max_left k _)).trans (hXtop _ (le_max_right k _)).le
  · cases j with
    | zero => exact ⟨0, hW0.trans hX0.symm⟩
    | succ j =>
      obtain ⟨k, hk⟩ := hXG (min (j + 1) N)
      refine ⟨k, ?_⟩
      rw [← hk]
      simp only [G, ite_eq_left (min_le_right _ N)]
      rcases le_total (j + 1) N with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, hN' _ h]
  · rw [hXm]
    intro M' hMM' hM'P
    by_contra hM'
    exact hMmax M' ⟨hWM.trans hMM', hM'P⟩ (lt_of_le_of_ne hMM' fun h => hM' (h ▸ le_rfl))

theorem exists_isotropicChain_refining [FiniteDimensional K V] (W : ℕ → Submodule K V)
    (hW0 : W 0 = ⊥) (hWmono : Monotone W) (hWiso : ∀ j, F.IsTotallyIsotropic (W j)) :
    ∃ (X : ℕ → Submodule K V) (m : ℕ), X 0 = ⊥ ∧ Monotone X ∧
      (∀ k, F.IsTotallyIsotropic (X k)) ∧ (∀ k ≤ m, Module.finrank K (X k) = k) ∧
      (∀ k, m ≤ k → X k = X m) ∧ (∀ j, ∃ k, W j = X k) ∧
      ∀ v ∈ F.perp (X m), F.β v v = 0 → v ∈ X m := by
  obtain ⟨X, m, hX0, hXmono, hXiso, hXrank, hXstable, hrefine, hmax⟩ :=
    exists_chain_refining_of_maximal (fun hM h => ReflForm.IsTotallyIsotropic.mono hM h) W hW0
      hWmono hWiso
  refine ⟨X, m, hX0, hXmono, hXiso, hXrank, hXstable, hrefine, fun v hv hvv => ?_⟩
  exact hmax _ le_sup_left ((hXiso m).sup_span hv hvv)
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))

end CFSG.LieType.BorelTits

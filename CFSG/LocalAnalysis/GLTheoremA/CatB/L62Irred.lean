module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.L62F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.L62F

open Matrix

theorem finite_end (X : Type) [AddCommGroup X] [Module (ZMod 2) X] [Finite X] :
    Finite (X →ₗ[ZMod 2] X) := by
  let b := Module.finBasis (ZMod 2) X
  have hinj : Function.Injective
      (fun f : X →ₗ[ZMod 2] X => fun i : Fin (Module.finrank (ZMod 2) X) => f (b i)) := by
    intro f g hfg; apply b.ext; intro i; exact congrFun hfg i
  exact Finite.of_injective _ hinj

@[expose] noncomputable def resHom (I : Subgroup Gx) (N : Submodule (ZMod 2) Vx)
    (hN : ∀ i ∈ I, ∀ n ∈ N, rho i n ∈ N) : I →* Module.End (ZMod 2) N where
  toFun i := (rho (i : Gx)).restrict (fun n hn => hN i i.2 n hn)
  map_one' := by ext n; simp
  map_mul' i j := by ext n; simp [map_mul]

@[expose] noncomputable def quotHom (I : Subgroup Gx) (N : Submodule (ZMod 2) Vx)
    (hN : ∀ i ∈ I, ∀ n ∈ N, rho i n ∈ N) : I →* Module.End (ZMod 2) (Vx ⧸ N) where
  toFun i := Submodule.mapQ N N (rho (i : Gx)) (fun n hn => hN i i.2 n hn)
  map_one' := by
    apply Submodule.linearMap_qext; ext v; simp
  map_mul' i j := by
    apply Submodule.linearMap_qext; ext v; simp [map_mul]

theorem hom_trivial_comm (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) {Q : Type} [AddCommGroup Q]
    [Module (ZMod 2) Q] [Module.Finite (ZMod 2) Q] [Finite Q] (hQ : Module.finrank (ZMod 2) Q = 4)
    (φ : I →* Module.End (ZMod 2) Q) (R : Q →ₗ[ZMod 2] Q) (hR : ∀ x, R (R x) + R x + x = 0)
    (hcomm : ∀ i x, φ i (R x) = R (φ i x)) (i : I) : φ i = 1 := by
  haveI := finite_end Q
  apply hom_trivial_of_small eI φ _ i
  have hle : Nat.card (Set.range φ) ≤
      Nat.card {f : Q →ₗ[ZMod 2] Q // ∀ x, f (R x) = R (f x)} := by
    have hinj : Function.Injective (fun f : Set.range φ =>
        (⟨f.1, by obtain ⟨j, hj⟩ := f.2; rw [← hj]; exact fun x => hcomm j x⟩ :
          {f : Q →ₗ[ZMod 2] Q // ∀ x, f (R x) = R (f x)})) := by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext hab
    exact Nat.card_le_card_of_injective _ hinj
  have hcomm_bound := comm_bound Q hQ R hR
  omega

theorem act_trivial_sub (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7))
    (N : Submodule (ZMod 2) Vx) (hN : ∀ i ∈ I, ∀ n ∈ N, rho i n ∈ N)
    (hsmall : Nat.card (Module.End (ZMod 2) N) < 2520) (i : I) (n : Vx) (hn : n ∈ N) :
    rho i n = n := by
  haveI := finite_end N
  have h1 := hom_trivial_of_small eI (resHom I N hN)
    (lt_of_le_of_lt (Nat.card_le_card_of_injective _ Subtype.val_injective) hsmall) i
  have h2 := congrArg (fun f : Module.End (ZMod 2) N => (f ⟨n, hn⟩ : Vx)) h1
  simpa [resHom] using h2

theorem act_trivial_quot (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7))
    (N : Submodule (ZMod 2) Vx) (hN : ∀ i ∈ I, ∀ n ∈ N, rho i n ∈ N)
    (hsmall : Nat.card (Module.End (ZMod 2) (Vx ⧸ N)) < 2520) (i : I) (v : Vx) :
    rho i v - v ∈ N := by
  haveI := finite_end (Vx ⧸ N)
  have h1 := hom_trivial_of_small eI (quotHom I N hN)
    (lt_of_le_of_lt (Nat.card_le_card_of_injective _ Subtype.val_injective) hsmall) i
  have h2 := congrArg (fun f : Module.End (ZMod 2) (Vx ⧸ N) => f (Submodule.Quotient.mk v)) h1
  simp only [quotHom, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.one_apply] at h2
  rw [Submodule.mapQ_apply] at h2
  exact (Submodule.Quotient.eq N).1 h2

theorem unipotent_false (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) (N : Submodule (ZMod 2) Vx)
    (h1 : ∀ i ∈ I, ∀ n ∈ N, rho i n = n) (h2 : ∀ i ∈ I, ∀ v, rho i v - v ∈ N) : False := by
  obtain ⟨c, hc3, hc1⟩ := exists_three_ne_one eI
  have hcI : (c : Gx) ∈ I := c.2
  have hc3' : (c : Gx) ^ 3 = 1 := by
    have := congrArg (fun g : I => (g : Gx)) hc3
    simpa using this
  have hx3 : rho (c : Gx) * rho (c : Gx) * rho (c : Gx) = 1 := by
    rw [← map_mul, ← map_mul, ← pow_three', hc3', map_one]
  have hsq : ∀ v, rho (c : Gx) (rho (c : Gx) v) = v := by
    intro v
    have hy := h1 c hcI _ (h2 c hcI v)
    rw [map_sub] at hy
    calc rho (c : Gx) (rho (c : Gx) v) = (rho (c : Gx) (rho (c : Gx) v) - rho (c : Gx) v) + rho (c : Gx) v := by
          abel
      _ = (rho (c : Gx) v - v) + rho (c : Gx) v := by rw [hy]
      _ = (rho (c : Gx) v + rho (c : Gx) v) - v := by abel
      _ = -v := by rw [hchar_Vx, zero_sub]
      _ = v := neg_eq_of_add_eq_zero_right (hchar_Vx v)
  have hid : ∀ v, rho (c : Gx) v = v := by
    intro v
    have h := hsq (rho (c : Gx) v)
    have h3 : rho (c : Gx) (rho (c : Gx) (rho (c : Gx) v)) = v := by
      have := congrArg (fun f : Ex => f v) hx3
      simpa [Module.End.mul_apply] using this
    rw [h3] at h
    exact h.symm
  apply hc1
  apply Subtype.ext
  rw [Subgroup.coe_one]
  apply rho_injective
  rw [map_one]
  exact LinearMap.ext (fun v => by simpa using hid v)

theorem finrank_Vx : Module.finrank (ZMod 2) Vx = 6 := by
  rw [Module.finrank_fintype_fun_eq_card]; simp [L62Model.ι, L62Model.ι₂]

theorem card_eq_two_pow (X : Type) [AddCommGroup X] [Module (ZMod 2) X] [Finite X] :
    Nat.card X = 2 ^ Module.finrank (ZMod 2) X := by
  haveI := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2)]
  simp

theorem end_card_le' (X : Type) [AddCommGroup X] [Module (ZMod 2) X] [Finite X] :
    Nat.card (X →ₗ[ZMod 2] X) ≤ (2 ^ Module.finrank (ZMod 2) X) ^ Module.finrank (ZMod 2) X := by
  rw [← card_eq_two_pow X]; exact card_end_le X

theorem small_end_bound (k : ℕ) (hk : k ≤ 3) : (2 ^ k) ^ k < 2520 := by
  interval_cases k <;> norm_num

theorem eps_comm {d i : Gx} (hc : ∀ v, rho i (rho d v) = rho d (rho i v)) (v : Vx) :
    rho i (epsE d v) = epsE d (rho i v) := by
  simp only [epsE_apply, map_add, hc]

theorem U_stable {d i : Gx} (hc : ∀ v, rho i (rho d v) = rho d (rho i v)) {u : Vx}
    (hu : u ∈ LinearMap.ker (epsE d)) : rho i u ∈ LinearMap.ker (epsE d) := by
  rw [LinearMap.mem_ker] at hu ⊢
  rw [← eps_comm hc, hu, map_zero]

theorem act_triv_U (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) {d : Gx}
    (hc : ∀ i ∈ I, ∀ v, rho i (rho d v) = rho d (rho i v))
    (hU2 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 2) (i : I) (u : Vx)
    (hu : u ∈ LinearMap.ker (epsE d)) : rho i u = u := by
  apply act_trivial_sub I eI _ (fun j hj n hn => U_stable (hc j hj) hn) _ i u hu
  have h := end_card_le' (LinearMap.ker (epsE d))
  rw [hU2] at h
  exact lt_of_le_of_lt h (small_end_bound 2 (by norm_num))

theorem U_span {d : Gx} (hd : d ^ 3 = 1) (hU2 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 2)
    {u : Vx} (hu : u ∈ LinearMap.ker (epsE d)) (hu0 : u ≠ 0) :
    ∀ x ∈ LinearMap.ker (epsE d), ∃ a b : ZMod 2, x = a • u + b • rho d u := by
  have hdu : rho d u ∈ LinearMap.ker (epsE d) := by
    rw [LinearMap.mem_ker] at hu ⊢; rw [epsE_rho hd, hu]
  have hli : LinearIndependent (ZMod 2) ![u, rho d u] := by
    rw [LinearIndependent.pair_iff' hu0]
    intro a hab
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) a with rfl | rfl
    · apply hu0
      have hb : rho d u = 0 := by simpa using hab.symm
      have h3 := rho_cube_apply hd u
      rw [hb, map_zero, map_zero] at h3
      exact h3.symm
    · apply hu0
      simp only [one_smul] at hab
      have hdeq : rho d u = u := hab.symm
      have h := hu
      rw [LinearMap.mem_ker, epsE_apply, hdeq, hdeq] at h
      rw [hchar_Vx, zero_add] at h
      exact h
  have hspan : Submodule.span (ZMod 2) (Set.range ![u, rho d u]) ≤ LinearMap.ker (epsE d) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact hu
    · exact hdu
  have hfin : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range ![u, rho d u])) = 2 := by
    rw [finrank_span_eq_card hli]; simp
  have heq := Submodule.eq_of_le_of_finrank_le hspan (by rw [hfin, hU2])
  intro x hx
  have hxmem : x ∈ Submodule.span (ZMod 2) (Set.range ![u, rho d u]) := by rw [heq]; exact hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hxmem
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp

theorem irr_W (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) {d : Gx} (hd : d ^ 3 = 1)
    (hc : ∀ i ∈ I, ∀ v, rho i (rho d v) = rho d (rho i v))
    (hU2 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 2)
    (M : Submodule (ZMod 2) Vx) (hMW : M ≤ LinearMap.range (epsE d))
    (hM : ∀ i ∈ I, ∀ m ∈ M, rho i m ∈ M) :
    M = ⊥ ∨ M = LinearMap.range (epsE d) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hrk := finrank_range_add_ker (d := d)
  have hWfin : Module.finrank (ZMod 2) (LinearMap.range (epsE d)) = 4 := by omega
  have hMpos : 0 < Module.finrank (ZMod 2) M := by
    apply Nat.pos_of_ne_zero; intro h0; exact h1 (Submodule.finrank_eq_zero.1 h0)
  have hMlt : Module.finrank (ZMod 2) M < 4 := by
    rw [← hWfin]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hMW h2)
  have hMU : M ⊓ LinearMap.ker (epsE d) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxW : x ∈ LinearMap.range (epsE d) ⊓ LinearMap.ker (epsE d) := ⟨hMW hx.1, hx.2⟩
    rw [range_inf_ker_eq_bot hd, Submodule.mem_bot] at hxW
    rw [Submodule.mem_bot]; exact hxW
  have hfinN : Module.finrank (ZMod 2) ↥(M ⊔ LinearMap.ker (epsE d)) = Module.finrank (ZMod 2) M + 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq M (LinearMap.ker (epsE d))
    rw [hMU, finrank_bot, hU2] at this
    omega
  have hquot : Module.finrank (ZMod 2) (Vx ⧸ (M ⊔ LinearMap.ker (epsE d))) ≤ 3 := by
    have := Submodule.finrank_quotient_add_finrank (M ⊔ LinearMap.ker (epsE d))
    rw [finrank_Vx] at this
    omega
  have hN : ∀ i ∈ I, ∀ n ∈ M ⊔ LinearMap.ker (epsE d), rho i n ∈ M ⊔ LinearMap.ker (epsE d) := by
    intro i hi n hn
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hn
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hM i hi y hy))
      (Submodule.mem_sup_right (U_stable (hc i hi) hz))
  have h1N : ∀ i ∈ I, ∀ n ∈ M ⊔ LinearMap.ker (epsE d), rho i n = n := by
    intro i hi n hn
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hn
    rw [map_add, act_trivial_sub I eI M hM
      (lt_of_le_of_lt (end_card_le' M) (small_end_bound _ (by omega))) ⟨i, hi⟩ y hy,
      act_triv_U I eI hc hU2 ⟨i, hi⟩ z hz]
  have h2N : ∀ i ∈ I, ∀ v, rho i v - v ∈ M ⊔ LinearMap.ker (epsE d) := fun i hi v =>
    act_trivial_quot I eI _ hN (lt_of_le_of_lt (end_card_le' _) (small_end_bound _ (by omega))) ⟨i, hi⟩ v
  exact unipotent_false I eI _ h1N h2N

theorem DI_list (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) {d : Gx} (hd : d ^ 3 = 1)
    (hc : ∀ i ∈ I, ∀ v, rho i (rho d v) = rho d (rho i v))
    (hU2 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 2)
    (M : Submodule (ZMod 2) Vx) (hMd : ∀ v ∈ M, rho d v ∈ M) (hMI : ∀ i ∈ I, ∀ m ∈ M, rho i m ∈ M) :
    M = ⊥ ∨ M = LinearMap.ker (epsE d) ∨ M = LinearMap.range (epsE d) ∨ M = ⊤ := by
  have hW : ∀ i ∈ I, ∀ w ∈ LinearMap.range (epsE d), rho i w ∈ LinearMap.range (epsE d) := by
    intro i hi w hw
    rw [range_eps_iff hd] at hw ⊢
    rw [← hc i hi w, hw]
  have hMW := irr_W I eI hd hc hU2 (M ⊓ LinearMap.range (epsE d)) inf_le_right
    (fun i hi m hm => ⟨hMI i hi m hm.1, hW i hi m hm.2⟩)
  have hMU : M ⊓ LinearMap.ker (epsE d) = ⊥ ∨ M ⊓ LinearMap.ker (epsE d) = LinearMap.ker (epsE d) := by
    by_cases hne : M ⊓ LinearMap.ker (epsE d) = ⊥
    · exact Or.inl hne
    · right
      obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 hne
      have hu2 : epsE d u = 0 := LinearMap.mem_ker.1 hu.2
      have hdu : rho d u ∈ M ⊓ LinearMap.ker (epsE d) :=
        ⟨hMd u hu.1, LinearMap.mem_ker.2 (by rw [epsE_rho hd, hu2])⟩
      apply le_antisymm inf_le_right
      intro x hx
      obtain ⟨a, b, rfl⟩ := U_span hd hU2 hu.2 hu0 x hx
      exact Submodule.add_mem _ (Submodule.smul_mem _ a hu) (Submodule.smul_mem _ b hdu)
  have hsplit : M = (M ⊓ LinearMap.range (epsE d)) ⊔ (M ⊓ LinearMap.ker (epsE d)) := by
    apply le_antisymm
    · intro v hv
      have hεv : epsE d v ∈ M := by
        rw [epsE_apply]
        exact Submodule.add_mem _ (Submodule.add_mem _ hv (hMd v hv)) (hMd _ (hMd v hv))
      have hvε : v - epsE d v ∈ M := Submodule.sub_mem _ hv hεv
      have h1 : epsE d v ∈ M ⊓ LinearMap.range (epsE d) := ⟨hεv, ⟨v, rfl⟩⟩
      have h2 : v - epsE d v ∈ M ⊓ LinearMap.ker (epsE d) := by
        exact ⟨hvε, LinearMap.mem_ker.2 (by rw [map_sub, epsE_eps hd, sub_self])⟩
      have := Submodule.add_mem_sup h1 h2
      rwa [add_sub_cancel] at this
    · exact sup_le inf_le_left inf_le_left
  rcases hMW with h1 | h1 <;> rcases hMU with h2 | h2
  · left; rw [hsplit, h1, h2, sup_bot_eq]
  · right; left; rw [hsplit, h1, h2, bot_sup_eq]
  · right; right; left; rw [hsplit, h1, h2, sup_bot_eq]
  · right; right; right; rw [hsplit, h1, h2, range_sup_ker_eq_top hd]

end CFSG.LocalAnalysis.GLTheoremA.CatB.L62F

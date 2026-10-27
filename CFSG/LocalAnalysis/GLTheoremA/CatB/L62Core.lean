module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.L62SAnalysis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.L62F

open Matrix

theorem quot_fixed (S : Subgroup Gx) (hS2 : IsPGroup 2 S) (X : Submodule (ZMod 2) Vx)
    (hX : ∀ g ∈ S, ∀ x ∈ X, rho g x = x) (hXne : X ≠ ⊤) :
    ∃ v, v ∉ X ∧ ∀ g ∈ S, rho g v - v ∈ X := by
  have hN : ∀ g ∈ S, ∀ n ∈ X, rho g n ∈ X := fun g hg n hn => by rw [hX g hg n hn]; exact hn
  letI : MulAction S (Vx ⧸ X) :=
    { smul := fun g q => quotHom S X hN g q
      one_smul := fun q => by
        change quotHom S X hN 1 q = q; rw [map_one]; rfl
      mul_smul := fun g h q => by
        change quotHom S X hN (g * h) q = quotHom S X hN g (quotHom S X hN h q)
        rw [map_mul]; rfl }
  have hdim : 0 < Module.finrank (ZMod 2) (Vx ⧸ X) := by
    have h1 := Submodule.finrank_quotient_add_finrank X
    have h2 := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.2 hXne)
    rw [finrank_top, finrank_Vx] at h2
    rw [finrank_Vx] at h1
    omega
  have hcard : 2 ∣ Nat.card (Vx ⧸ X) := by
    rw [card_eq_two_pow]; exact dvd_pow_self 2 (by omega)
  obtain ⟨q, hq0, hqfix⟩ := fixed_point_ne hS2 (0 : Vx ⧸ X) (fun h => by
    change quotHom S X hN h 0 = 0; rw [map_zero]) hcard
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective X q
  refine ⟨v, fun hv => hq0 ((Submodule.Quotient.mk_eq_zero X).2 hv), fun g hg => ?_⟩
  have h1 := hqfix ⟨g, hg⟩
  have h2 : quotHom S X hN ⟨g, hg⟩ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := h1
  have h3 : (Submodule.Quotient.mk (rho g v) : Vx ⧸ X) = Submodule.Quotient.mk v := by
    simpa [quotHom, Submodule.mapQ_apply] using h2
  exact (Submodule.Quotient.eq X).1 h3

def fixSub (S : Subgroup Gx) : Submodule (ZMod 2) Vx where
  carrier := {v | ∀ g ∈ S, rho g v = v}
  add_mem' := fun {a b} ha hb g hg => by
    simp only [Set.mem_setOf_eq, map_add] at *; rw [ha g hg, hb g hg]
  zero_mem' := fun g _ => by simp
  smul_mem' := fun c a ha g hg => by
    simp only [Set.mem_setOf_eq, map_smul] at *; rw [ha g hg]

theorem mem_fixSub {S : Subgroup Gx} {v : Vx} : v ∈ fixSub S ↔ ∀ g ∈ S, rho g v = v := Iff.rfl

theorem fixSub_ne_top {S : Subgroup Gx} (hS : S ≠ ⊥) : fixSub S ≠ ⊤ := by
  intro h
  apply hS
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply rho_injective
  rw [map_one]
  apply LinearMap.ext
  intro v
  have hv : v ∈ fixSub S := by rw [h]; exact Submodule.mem_top
  exact (mem_fixSub.1 hv) g hg

theorem triv_quot_of_eq_one (I : Subgroup Gx) (N : Submodule (ZMod 2) Vx)
    (hN : ∀ i ∈ I, ∀ n ∈ N, rho i n ∈ N) (i : I) (hφ : quotHom I N hN i = 1) (v : Vx) :
    rho i v - v ∈ N := by
  have h2 := congrArg (fun f : Module.End (ZMod 2) (Vx ⧸ N) => f (Submodule.Quotient.mk v)) hφ
  simp only [quotHom, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.one_apply] at h2
  rw [Submodule.mapQ_apply] at h2
  exact (Submodule.Quotient.eq N).1 h2

theorem no_m2 (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) {d : Gx} (hd : d ^ 3 = 1)
    (hc : ∀ i ∈ I, ∀ v, rho i (rho d v) = rho d (rho i v))
    (hU4 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 4) : False := by
  have hrk := finrank_range_add_ker (d := d)
  have hWI : ∀ i ∈ I, ∀ w ∈ LinearMap.range (epsE d), rho i w ∈ LinearMap.range (epsE d) := by
    intro i hi w hw
    rw [range_eps_iff hd] at hw ⊢
    rw [← hc i hi w, hw]
  have hUI : ∀ i ∈ I, ∀ u ∈ LinearMap.ker (epsE d), rho i u ∈ LinearMap.ker (epsE d) :=
    fun i hi u hu => U_stable (hc i hi) hu
  have hW2 : Module.finrank (ZMod 2) (LinearMap.range (epsE d)) = 2 := by omega
  have htW : ∀ i ∈ I, ∀ w ∈ LinearMap.range (epsE d), rho i w = w := fun i hi w hw =>
    act_trivial_sub I eI _ hWI (lt_of_le_of_lt (end_card_le' _) (by rw [hW2]; norm_num)) ⟨i, hi⟩ w hw
  let RU : LinearMap.ker (epsE d) →ₗ[ZMod 2] LinearMap.ker (epsE d) :=
    (rho d).restrict (fun u hu => by
      rw [LinearMap.mem_ker] at hu ⊢
      rw [epsE_rho hd, hu])
  have hRU : ∀ x, RU (RU x) + RU x + x = 0 := by
    intro x
    apply Subtype.ext
    have h := LinearMap.mem_ker.1 x.2
    rw [epsE_apply] at h
    show rho d (rho d x) + rho d x + x = 0
    calc rho d (rho d x) + rho d x + x = x + rho d x + rho d (rho d x) := by abel
      _ = 0 := h
  have htU : ∀ i ∈ I, ∀ u ∈ LinearMap.ker (epsE d), rho i u = u := by
    intro i hi u hu
    have h1 := hom_trivial_comm I eI (Q := ↥(LinearMap.ker (epsE d))) hU4
      (resHom I _ hUI) RU hRU (fun j x => by
        apply Subtype.ext
        exact hc j j.2 x.1) ⟨i, hi⟩
    have h2 := congrArg (fun f : Module.End (ZMod 2) (LinearMap.ker (epsE d)) => (f ⟨u, hu⟩ : Vx)) h1
    simpa [resHom] using h2
  obtain ⟨c, _, hc1⟩ := exists_three_ne_one eI
  apply hc1
  apply Subtype.ext
  rw [Subgroup.coe_one]
  apply rho_injective
  rw [map_one]
  apply LinearMap.ext
  intro v
  have hv : v = epsE d v + (v - epsE d v) := by abel
  have hW' : epsE d v ∈ LinearMap.range (epsE d) := ⟨v, rfl⟩
  have hU' : v - epsE d v ∈ LinearMap.ker (epsE d) :=
    LinearMap.mem_ker.2 (by rw [map_sub, epsE_eps hd, sub_self])
  calc rho (c : Gx) v = rho (c : Gx) (epsE d v) + rho (c : Gx) (v - epsE d v) := by
        rw [← map_add, add_sub_cancel]
    _ = epsE d v + (v - epsE d v) := by
        rw [htW (c : Gx) c.2 _ hW', htU (c : Gx) c.2 _ hU']
    _ = v := by abel

theorem no_m3 (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) {d : Gx} (hd : d ^ 3 = 1)
    (hc : ∀ i ∈ I, ∀ v, rho i (rho d v) = rho d (rho i v))
    (hU6 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 6)
    (M : Submodule (ZMod 2) Vx) (hMd : ∀ v ∈ M, rho d v ∈ M) (hMI : ∀ i ∈ I, ∀ m ∈ M, rho i m ∈ M) :
    M = ⊥ ∨ M = ⊤ := by
  have hKtop : LinearMap.ker (epsE d) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simp [hU6, finrank_Vx])
  have hεv : ∀ v, v + rho d v + rho d (rho d v) = 0 := fun v => by
    have h : epsE d v = 0 := LinearMap.mem_ker.1 (hKtop ▸ Submodule.mem_top)
    rwa [epsE_apply] at h
  have hfix : ∀ v, rho d v = v → v = 0 := fun v hv => by
    have h := hεv v
    rw [hv, hv, hchar_Vx, zero_add] at h
    exact h
  have hk := Submodule.finrank_quotient_add_finrank M
  rw [finrank_Vx] at hk
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hpos : 0 < Module.finrank (ZMod 2) M :=
    Nat.pos_of_ne_zero (fun h0 => h1 (Submodule.finrank_eq_zero.1 h0))
  have hlt : Module.finrank (ZMod 2) M < 6 := by
    have := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.2 h2)
    rwa [finrank_top, finrank_Vx] at this
  rcases (show Module.finrank (ZMod 2) M = 1 ∨ Module.finrank (ZMod 2) M = 2 ∨
      Module.finrank (ZMod 2) M = 3 ∨ Module.finrank (ZMod 2) M = 4 ∨
      Module.finrank (ZMod 2) M = 5 by omega) with k | k | k | k | k
  ·
    obtain ⟨m, hm0, hspan⟩ := finrank_eq_one_iff'.1 k
    obtain ⟨c, hc'⟩ := hspan ⟨rho d m, hMd _ m.2⟩
    have hc'' : c • (m : Vx) = rho d m := congrArg Subtype.val hc'
    have hm := hεv m
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) c with rfl | rfl
    · rw [zero_smul] at hc''
      rw [← hc''] at hm
      simp at hm
      exact hm0 hm
    · rw [one_smul] at hc''
      exact hm0 (Subtype.ext (hfix m hc''.symm))
  ·
    have h1' : ∀ i ∈ I, ∀ n ∈ M, rho i n = n := fun i hi n hn =>
      act_trivial_sub I eI M hMI (lt_of_le_of_lt (end_card_le' M) (by rw [k]; exact small_end_bound 2 (by norm_num)))
        ⟨i, hi⟩ n hn
    have hMd' : M ≤ M.comap (rho d) := fun v hv => hMd v hv
    let R : (Vx ⧸ M) →ₗ[ZMod 2] (Vx ⧸ M) := Submodule.mapQ M M (rho d) hMd'
    have hR : ∀ x, R (R x) + R x + x = 0 := by
      intro x
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective M x
      have hz : rho d (rho d v) + rho d v + v = 0 := by
        rw [show rho d (rho d v) + rho d v + v = v + rho d v + rho d (rho d v) by abel]
        exact hεv v
      exact (Submodule.Quotient.mk_eq_zero M).2 (by simpa [hz] using M.zero_mem)
    have hcomm : ∀ (i : I) (x : Vx ⧸ M), quotHom I M hMI i (R x) = R (quotHom I M hMI i x) := by
      intro i x
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective M x
      show Submodule.Quotient.mk (rho (i : Gx) (rho d v)) = Submodule.Quotient.mk (rho d (rho (i : Gx) v))
      rw [hc (i : Gx) i.2 v]
    have hQ : Module.finrank (ZMod 2) (Vx ⧸ M) = 4 := by omega
    have hφ := hom_trivial_comm I eI hQ (quotHom I M hMI) R hR hcomm
    exact unipotent_false I eI M h1' (fun i hi v => triv_quot_of_eq_one I M hMI ⟨i, hi⟩
      (hφ ⟨i, hi⟩) v)
  ·
    exact unipotent_false I eI M
      (fun i hi n hn => act_trivial_sub I eI M hMI
        (lt_of_le_of_lt (end_card_le' M) (by rw [k]; exact small_end_bound 3 (by norm_num))) ⟨i, hi⟩ n hn)
      (fun i hi v => act_trivial_quot I eI M hMI
        (lt_of_le_of_lt (end_card_le' _) (by
          rw [show Module.finrank (ZMod 2) (Vx ⧸ M) = 3 by omega]; exact small_end_bound 3 (by norm_num)))
        ⟨i, hi⟩ v)
  ·
    have h2' : ∀ i ∈ I, ∀ v, rho i v - v ∈ M := fun i hi v => act_trivial_quot I eI M hMI
      (lt_of_le_of_lt (end_card_le' _) (by
        rw [show Module.finrank (ZMod 2) (Vx ⧸ M) = 2 by omega]; exact small_end_bound 2 (by norm_num)))
      ⟨i, hi⟩ v
    let R : M →ₗ[ZMod 2] M := (rho d).restrict (fun n hn => hMd n hn)
    have hR : ∀ x, R (R x) + R x + x = 0 := by
      intro x
      apply Subtype.ext
      have h := hεv x.1
      show rho d (rho d x.1) + rho d x.1 + x.1 = 0
      rw [show rho d (rho d x.1) + rho d x.1 + x.1 = x.1 + rho d x.1 + rho d (rho d x.1) by abel]
      exact h
    have hcomm : ∀ (i : I) (x : M), resHom I M hMI i (R x) = R (resHom I M hMI i x) := by
      intro i x
      apply Subtype.ext
      exact hc (i : Gx) i.2 x.1
    have hφ := hom_trivial_comm I eI (Q := ↥M) k (resHom I M hMI) R hR hcomm
    exact unipotent_false I eI M (fun i hi n hn => by
      have := congrArg (fun f : Module.End (ZMod 2) M => (f ⟨n, hn⟩ : Vx)) (hφ ⟨i, hi⟩)
      simpa [resHom] using this) h2'
  ·
    have hQ1 : Module.finrank (ZMod 2) (Vx ⧸ M) = 1 := by omega
    obtain ⟨q, hq0, hspan⟩ := finrank_eq_one_iff'.1 hQ1
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective M q
    have hxM : x ∉ M := fun h => hq0 ((Submodule.Quotient.mk_eq_zero M).2 h)
    have hdx : rho d x - x ∈ M := by
      obtain ⟨c, hc1⟩ := hspan (Submodule.Quotient.mk (rho d x))
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hc1
        have hmem : rho d x ∈ M := (Submodule.Quotient.mk_eq_zero M).1 hc1.symm
        apply hxM
        have key : x = rho d (rho d x) + rho d x := by
          have h2x := hchar_Vx (rho d x)
          have h3x := hchar_Vx (rho d (rho d x))
          calc x = x + (rho d x + rho d x) + (rho d (rho d x) + rho d (rho d x)) := by
                rw [h2x, h3x, add_zero, add_zero]
            _ = (x + rho d x + rho d (rho d x)) + (rho d x + rho d (rho d x)) := by abel
            _ = rho d (rho d x) + rho d x := by rw [hεv x]; abel
        rw [key]
        exact M.add_mem (hMd _ hmem) hmem
      have hc1' : c = 1 := by
        rcases (show ∀ y : ZMod 2, y ≠ 0 → y = 1 from by decide) c hc0 with h
        exact h
      rw [hc1', one_smul] at hc1
      exact (Submodule.Quotient.eq M).1 hc1.symm
    have hall : ∀ v, rho d v - v ∈ M := by
      intro v
      obtain ⟨c, hcv⟩ := hspan (Submodule.Quotient.mk v)
      have hm0 : v - c • x ∈ M := by
        have := (Submodule.Quotient.eq M).1 (show Submodule.Quotient.mk (c • x) = Submodule.Quotient.mk v from by
          rw [Submodule.Quotient.mk_smul]; exact hcv)
        rw [← neg_sub]; exact M.neg_mem this
      have hsplit : rho d v - v = (rho d (v - c • x) - (v - c • x)) + c • (rho d x - x) := by
        rw [map_sub, map_smul]; module
      rw [hsplit]
      exact M.add_mem (M.sub_mem (hMd _ hm0) hm0) (M.smul_mem c hdx)
    have hinj : Function.Injective (rho d - LinearMap.id : Ex) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      apply hfix v
      simp only [LinearMap.sub_apply, LinearMap.id_apply] at hv
      exact sub_eq_zero.1 hv
    have hsurj := LinearMap.injective_iff_surjective.1 hinj
    apply h2
    rw [eq_top_iff]
    intro y _
    obtain ⟨v, hv⟩ := hsurj y
    have hy : y = rho d v - v := by
      rw [← hv]; simp
    rw [hy]; exact hall v

theorem rho_mul_inv_apply (n : Gx) (x : Vx) : rho n (rho n⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem wstab {d g : Gx} (hd : d ^ 3 = 1) (hg : ∀ v, rho g (rho d v) = rho d (rho g v)) {w : Vx}
    (hw : w ∈ LinearMap.range (epsE d)) : rho g w ∈ LinearMap.range (epsE d) := by
  rw [range_eps_iff hd] at hw ⊢
  rw [← hg w, hw]

theorem isHW_conj {d j : Gx} (hd : d ^ 3 = 1) (hj : ∀ v, rho j (rho d v) = rho d (rho j v))
    (hj' : ∀ v, rho j⁻¹ (rho d v) = rho d (rho j⁻¹ v)) {h : Ex} (hh : IsHW d h) :
    IsHW d (rho j * h * rho j⁻¹) :=
  by
    unfold IsHW at hh ⊢
    exact ⟨fun v => wstab hd hj (hh.1 _), fun w hw => by
      show rho j (h (rho j⁻¹ w)) = 0
      rw [hh.2 _ (wstab hd hj' hw), map_zero]⟩

theorem isHU_conj {d j : Gx} (hj : ∀ v, rho j (rho d v) = rho d (rho j v))
    (hj' : ∀ v, rho j⁻¹ (rho d v) = rho d (rho j⁻¹ v)) {h : Ex} (hh : IsHU d h) :
    IsHU d (rho j * h * rho j⁻¹) :=
  by
    unfold IsHU at hh ⊢
    exact ⟨fun v => U_stable hj (hh.1 _), fun u hu => by
      show rho j (h (rho j⁻¹ u)) = 0
      rw [hh.2 _ (U_stable hj' hu), map_zero]⟩

def Fsub (S : Subgroup Gx) (X : Submodule (ZMod 2) Vx) : Submodule (ZMod 2) Vx where
  carrier := {v | ∀ g ∈ S, rho g v - v ∈ X}
  add_mem' := fun {a b} ha hb g hg => by
    rw [map_add, show rho g a + rho g b - (a + b) = (rho g a - a) + (rho g b - b) by abel]
    exact X.add_mem (ha g hg) (hb g hg)
  zero_mem' := fun g _ => by rw [map_zero, sub_zero]; exact X.zero_mem
  smul_mem' := fun c a ha g hg => by
    rw [map_smul, ← smul_sub]; exact X.smul_mem c (ha g hg)

theorem rho_mul_inv_self (n : Gx) : rho n * rho n⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem conj_sub_identity (n g : Gx) (v : Vx) :
    rho g (rho n v) - rho n v = rho n (rho (n⁻¹ * g * n) v - v) := by
  simp only [map_sub, map_mul, Module.End.mul_apply, rho_mul_inv_apply]

theorem fixSub_ne_bot (S : Subgroup Gx) (hS2 : IsPGroup 2 S) : fixSub S ≠ ⊥ := by
  intro h0
  letI : MulAction S Vx := actV S
  have hfp := fixed_point_ne hS2 (0 : Vx) (fun h => map_zero (rho (h : Gx))) (show 2 ∣ Nat.card Vx by
    rw [card_eq_two_pow, finrank_Vx]; norm_num)
  obtain ⟨a, ha0, hafix⟩ := hfp
  have haX : a ∈ fixSub S := mem_fixSub.2 (fun g hg => hafix ⟨g, hg⟩)
  rw [h0, Submodule.mem_bot] at haX
  exact ha0 haX

theorem fixSub_norm {S : Subgroup Gx} {n : Gx} (hn : n ∈ Subgroup.normalizer (S : Set Gx)) {v : Vx}
    (hv : v ∈ fixSub S) : rho n v ∈ fixSub S := by
  rw [mem_fixSub]
  intro s hs
  have h1 : n⁻¹ * s * n⁻¹⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) s).1 hs
  rw [inv_inv] at h1
  have h2 := mem_fixSub.1 hv _ h1
  calc rho s (rho n v) = rho n (rho (n⁻¹ * s * n) v) := by
        simp only [map_mul, Module.End.mul_apply, rho_mul_inv_apply]
    _ = rho n v := by rw [h2]

theorem comm_pointwise {x y : Gx} (h : x * y = y * x) (v : Vx) : rho y (rho x v) = rho x (rho y v) := by
  have := congrArg (fun g : Gx => rho g v) h
  simp only [map_mul, Module.End.mul_apply] at this
  exact this.symm

theorem S_generic (I : Subgroup Gx) {d : Gx} (hd : d ^ 3 = 1)
    (S : Subgroup Gx) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hdS : d ∈ Subgroup.normalizer (S : Set Gx))
    (hIS : ∀ i ∈ I, i ∈ Subgroup.normalizer (S : Set Gx))
    (j : Gx) (hj : ∀ v, rho j (rho d v) = rho d (rho j v))
    (hj' : ∀ v, rho j⁻¹ (rho d v) = rho d (rho j⁻¹ v))
    (X : Submodule (ZMod 2) Vx) (hXeq : ∀ v, v ∈ X ↔ ∀ g ∈ S, rho g v = v) (hX0 : X ≠ ⊥) (hXne : X ≠ ⊤)
    (hXd : ∀ v ∈ X, rho d v ∈ X) (hXI : ∀ i ∈ I, ∀ m ∈ X, rho i m ∈ X)
    (hlist : ∀ F : Submodule (ZMod 2) Vx, (∀ v ∈ F, rho d v ∈ F) → (∀ i ∈ I, ∀ v ∈ F, rho i v ∈ F) →
      (∀ v ∈ X, v ∈ F) → F ≠ X → F = ⊤)
    (P0 : Ex → Prop) (hP0X : ∀ h : Ex, (∀ v, h v ∈ X) → (∀ x ∈ X, h x = 0) → P0 h)
    (hL : ∀ T : Submodule (ZMod 2) Ex, (∀ h ∈ T, P0 h) → (∀ i ∈ I, ∀ h ∈ T, rho i * h * rho i⁻¹ ∈ T) →
      (∀ h ∈ T, rho d * h * (rho d * rho d) ∈ T) → (∀ h ∈ T, rho d * rho d * h * rho d ∈ T) →
      (∀ h ∈ T, h = 0) ∨ (∀ h : Ex, P0 h → h ∈ T))
    (hPconj : ∀ k : Gx, (∀ v, rho k (rho d v) = rho d (rho k v)) →
      (∀ v, rho k⁻¹ (rho d v) = rho d (rho k⁻¹ v)) → ∀ h, P0 h → P0 (rho k * h * rho k⁻¹)) :
    j ∈ Subgroup.normalizer (S : Set Gx) := by
  have hN : ∀ n ∈ Subgroup.normalizer (S : Set Gx), ∀ g ∈ S, n * g * n⁻¹ ∈ S :=
    fun n hn g hg => (Subgroup.mem_normalizer_iff.1 hn g).1 hg
  have hNinv : ∀ n ∈ Subgroup.normalizer (S : Set Gx), ∀ g ∈ S, n⁻¹ * g * n ∈ S := fun n hn g hg => by
    have := hN n⁻¹ (Subgroup.inv_mem _ hn) g hg
    rwa [inv_inv] at this
  have hXfix : ∀ g ∈ S, ∀ x ∈ X, rho g x = x := fun g hg x hx => (hXeq x).1 hx g hg
  let F := Fsub S X
  have hFd : ∀ v ∈ F, rho d v ∈ F := fun v hv g hg => by
    rw [conj_sub_identity d g v]
    exact hXd _ (hv _ (hNinv d hdS g hg))
  have hFI : ∀ i ∈ I, ∀ v ∈ F, rho i v ∈ F := fun i hi v hv g hg => by
    rw [conj_sub_identity i g v]
    exact hXI i hi _ (hv _ (hNinv i (hIS i hi) g hg))
  obtain ⟨v0, hv0X, hv0F⟩ := quot_fixed S hS2 X hXfix hXne
  have hFne : Fsub S X ≠ X := by
    intro hFX
    apply hv0X
    have hv0F' : v0 ∈ Fsub S X := hv0F
    rw [hFX] at hv0F'
    exact hv0F'
  have hXF : ∀ v ∈ X, v ∈ Fsub S X := fun v hv g hg => by
    rw [hXfix g hg v hv, sub_self]; exact X.zero_mem
  have hFtop : Fsub S X = ⊤ := hlist (Fsub S X) hFd hFI hXF hFne
  have hF : ∀ g ∈ S, ∀ v, rho g v - v ∈ X := fun g hg v => by
    have hv : v ∈ Fsub S X := by rw [hFtop]; exact Submodule.mem_top
    exact hv g hg
  have hAX : ∀ g ∈ S, ∀ a : Ex, rho g = 1 + a → (∀ v, a v ∈ X) ∧ (∀ x ∈ X, a x = 0) := by
    intro g hg a ha
    refine ⟨fun v => ?_, fun x hx => ?_⟩
    · have h2 : a v = rho g v - v := by
        rw [ha, LinearMap.add_apply, Module.End.one_apply]; abel
      rw [h2]; exact hF g hg v
    · have h1 : rho g x = x := hXfix g hg x hx
      rw [ha, LinearMap.add_apply, Module.End.one_apply] at h1
      simpa using h1
  have hab : ∀ a b : Ex, (∀ v, b v ∈ X) → (∀ x ∈ X, a x = 0) → a * b = 0 := fun a b hb ha =>
    LinearMap.ext fun v => by rw [Module.End.mul_apply, ha _ (hb v), LinearMap.zero_apply]
  let T : Submodule (ZMod 2) Ex :=
    { carrier := {h | ∃ g ∈ S, rho g = 1 + h}
      add_mem' := by
        rintro a b ⟨g, hg, hga⟩ ⟨g', hg', hgb⟩
        refine ⟨g * g', S.mul_mem hg hg', ?_⟩
        obtain ⟨hb1, _⟩ := hAX g' hg' b hgb
        obtain ⟨_, ha2⟩ := hAX g hg a hga
        rw [map_mul, hga, hgb]
        simp only [add_mul, mul_add, one_mul, mul_one]
        rw [hab a b hb1 ha2]
        abel
      zero_mem' := ⟨1, S.one_mem, by simp⟩
      smul_mem' := by
        rintro c a ⟨g, hg, hga⟩
        rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) c with rfl | rfl
        · exact ⟨1, S.one_mem, by simp⟩
        · exact ⟨g, hg, by simp [hga]⟩ }
  have hTconj : ∀ n ∈ Subgroup.normalizer (S : Set Gx), ∀ h ∈ T, rho n * h * rho n⁻¹ ∈ T := by
    rintro n hn h ⟨g, hg, hgh⟩
    refine ⟨n * g * n⁻¹, hN n hn g hg, ?_⟩
    rw [map_mul, map_mul, hgh, mul_add, add_mul, mul_one, rho_mul_inv_self n]
  have hT0 : ∀ h ∈ T, P0 h := by
    rintro h ⟨g, hg, hgh⟩
    obtain ⟨h1, h2⟩ := hAX g hg h hgh
    exact hP0X h h1 h2
  have hdd : d * d = d⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hd)
  have e : rho d⁻¹ = rho d * rho d := by rw [← map_mul, hdd]
  have hTd1 : ∀ h ∈ T, rho d * h * (rho d * rho d) ∈ T := fun h hh => by
    have := hTconj d hdS h hh
    rwa [← e] 
  have hTd2 : ∀ h ∈ T, rho d * rho d * h * rho d ∈ T := fun h hh => by
    have := hTconj d⁻¹ (Subgroup.inv_mem _ hdS) h hh
    rwa [inv_inv, e] at this
  rcases hL T hT0 (fun i hi h hh => hTconj i (hIS i hi) h hh) hTd1 hTd2 with hz | hall'
  · exfalso
    apply hS1
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have h0 := hz (rho g - 1) ⟨g, hg, by abel⟩
    apply rho_injective
    rw [map_one]
    exact sub_eq_zero.1 h0
  have hall : ∀ h : Ex, P0 h → ∃ g ∈ S, rho g = 1 + h := fun h hh => hall' h hh
  have hPS : ∀ g ∈ S, P0 (rho g - 1) := fun g hg =>
    hP0X _ (fun v => by rw [LinearMap.sub_apply, Module.End.one_apply]; exact hF g hg v)
      (fun x hx => by rw [LinearMap.sub_apply, Module.End.one_apply, hXfix g hg x hx, sub_self])
  have forward : ∀ k : Gx, (∀ h, P0 h → P0 (rho k * h * rho k⁻¹)) → ∀ g ∈ S, k * g * k⁻¹ ∈ S := by
    intro k hk g hg
    have h1 := hk _ (hPS g hg)
    have h2 : rho k * (rho g - 1) * rho k⁻¹ = rho (k * g * k⁻¹) - 1 := by
      simp only [mul_sub, sub_mul, mul_one, rho_mul_inv_self k, map_mul]
    rw [h2] at h1
    obtain ⟨g', hg', hg'eq⟩ := hall _ h1
    have h3 : rho g' = rho (k * g * k⁻¹) := by rw [hg'eq]; abel
    rwa [rho_injective h3] at hg'
  have hjc : ∀ h, P0 h → P0 (rho j * h * rho j⁻¹) := fun h hh => hPconj j hj hj' h hh
  have hjc' : ∀ h, P0 h → P0 (rho j⁻¹ * h * rho j⁻¹⁻¹) := fun h hh =>
    hPconj j⁻¹ hj' (by rw [inv_inv]; exact hj) h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact forward j hjc g hg
  · intro hg
    have := forward j⁻¹ hjc' _ hg
    have e2 : j⁻¹ * (j * g * j⁻¹) * j⁻¹⁻¹ = g := by group
    rwa [e2] at this

theorem S_analysis (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) {d : Gx} (hd : d ^ 3 = 1)
    (hc : ∀ i ∈ I, ∀ v, rho i (rho d v) = rho d (rho i v))
    (hU2 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 2)
    (S : Subgroup Gx) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hdS : d ∈ Subgroup.normalizer (S : Set Gx)) (hIS : ∀ i ∈ I, i ∈ Subgroup.normalizer (S : Set Gx))
    (j : Gx) (hj : ∀ v, rho j (rho d v) = rho d (rho j v))
    (hj' : ∀ v, rho j⁻¹ (rho d v) = rho d (rho j⁻¹ v)) :
    j ∈ Subgroup.normalizer (S : Set Gx) := by
  have hX0 := fixSub_ne_bot S hS2
  have hXne := fixSub_ne_top hS1
  have hXd : ∀ v ∈ fixSub S, rho d v ∈ fixSub S := fun v hv => fixSub_norm hdS hv
  have hXI : ∀ i ∈ I, ∀ m ∈ fixSub S, rho i m ∈ fixSub S := fun i hi m hm => fixSub_norm (hIS i hi) hm
  rcases DI_list I eI hd hc hU2 (fixSub S) hXd hXI with hX | hX | hX | hX
  · exact absurd hX hX0
  ·
    refine S_generic I hd S hS2 hS1 hdS hIS j hj hj' (fixSub S) (fun v => mem_fixSub) hX0 hXne hXd hXI ?_
      (IsHU d) (fun h h1 h2 => by rw [hX] at h1 h2; exact ⟨h1, h2⟩)
      (fun T h0 hi hd1 hd2 => lemmaB I eI hd hc hU2 T h0 hi hd1 hd2)
      (fun k hk hk' h hh => isHU_conj hk hk' hh)
    intro F hFd hFI hXF hFne
    rcases DI_list I eI hd hc hU2 F hFd hFI with h | h | h | h
    · exfalso; apply hX0; rw [eq_bot_iff]; intro v hv; rw [Submodule.mem_bot]
      have := hXF v hv; rw [h] at this; exact (Submodule.mem_bot _).1 this
    · exact absurd (h.trans hX.symm) hFne
    · exfalso
      have hle : fixSub S ≤ LinearMap.range (epsE d) := fun v hv => by
        have := hXF v hv; rw [h] at this; exact this
      apply hX0
      rw [hX] at hle ⊢
      have : LinearMap.ker (epsE d) = LinearMap.ker (epsE d) ⊓ LinearMap.range (epsE d) :=
        (inf_eq_left.2 hle).symm
      rw [inf_comm, range_inf_ker_eq_bot hd] at this
      exact this
    · exact h
  ·
    refine S_generic I hd S hS2 hS1 hdS hIS j hj hj' (fixSub S) (fun v => mem_fixSub) hX0 hXne hXd hXI ?_
      (IsHW d) (fun h h1 h2 => by rw [hX] at h1 h2; exact ⟨h1, h2⟩)
      (fun T h0 hi hd1 hd2 => lemmaA I eI hd hc hU2 T h0 hi hd1 hd2)
      (fun k hk hk' h hh => isHW_conj hd hk hk' hh)
    intro F hFd hFI hXF hFne
    rcases DI_list I eI hd hc hU2 F hFd hFI with h | h | h | h
    · exfalso; apply hX0; rw [eq_bot_iff]; intro v hv; rw [Submodule.mem_bot]
      have := hXF v hv; rw [h] at this; exact (Submodule.mem_bot _).1 this
    · exfalso
      have hle : fixSub S ≤ LinearMap.ker (epsE d) := fun v hv => by
        have := hXF v hv; rw [h] at this; exact this
      apply hX0
      rw [hX] at hle ⊢
      have : LinearMap.range (epsE d) = LinearMap.range (epsE d) ⊓ LinearMap.ker (epsE d) :=
        (inf_eq_left.2 hle).symm
      rw [range_inf_ker_eq_bot hd] at this
      exact this
    · exact absurd (h.trans hX.symm) hFne
    · exact h
  · exact absurd hX hXne

end CFSG.LocalAnalysis.GLTheoremA.CatB.L62F

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.LocalAnalysis.GLTheoremA.CatB.L62F

theorem l62Core_holds : L62Core := by
  intro D I J S hD hIJ hDI hDJ hI7 hJ8 hS hS2 hDN hIN
  obtain ⟨eI⟩ := hI7
  haveI : Nontrivial D := Finite.one_lt_card_iff_nontrivial.1 (by rw [hD]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : D)
  have hx3 : x ^ 3 = 1 := by
    have := pow_card_eq_one' (G := D) (x := x)
    rwa [hD] at this
  obtain ⟨d, hdD, hd3, hd1⟩ : ∃ d : Gx, d ∈ D ∧ d ^ 3 = 1 ∧ d ≠ 1 :=
    ⟨x, x.2, by simpa using congrArg Subtype.val hx3, fun h => hx (Subtype.ext h)⟩
  have hc : ∀ i ∈ I, ∀ v, rho i (rho d v) = rho d (rho i v) := fun i hi v =>
    comm_pointwise (hDI d hdD i hi) v
  have hcJ : ∀ j ∈ J, ∀ v, rho j (rho d v) = rho d (rho j v) := fun j hj v =>
    comm_pointwise (hDJ d hdD j hj) v
  have hcJ' : ∀ j ∈ J, ∀ v, rho j⁻¹ (rho d v) = rho d (rho j⁻¹ v) := fun j hj v =>
    comm_pointwise (hDJ d hdD j⁻¹ (J.inv_mem hj)) v
  intro j hj
  obtain ⟨r, hr⟩ := even_finrank_range hd3 hd1
  have hsum := finrank_range_add_ker (d := d)
  have hWtop : LinearMap.range (epsE d) = ⊤ → d = 1 := fun htop => by
    apply rho_injective
    rw [map_one]
    apply LinearMap.ext
    intro v
    have hv : v ∈ LinearMap.range (epsE d) := by rw [htop]; exact Submodule.mem_top
    rw [Module.End.one_apply]
    exact (range_eps_iff hd3 v).1 hv
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with h0 | h1 | h2 | h3
  ·
    exfalso
    have hU6 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 6 := by omega
    have hXd : ∀ v ∈ CFSG.LocalAnalysis.GLTheoremA.CatB.L62F.fixSub S, rho d v ∈ CFSG.LocalAnalysis.GLTheoremA.CatB.L62F.fixSub S := fun v hv => CFSG.LocalAnalysis.GLTheoremA.CatB.L62F.fixSub_norm (hDN hdD) hv
    have hXI : ∀ i ∈ I, ∀ m ∈ CFSG.LocalAnalysis.GLTheoremA.CatB.L62F.fixSub S, rho i m ∈ CFSG.LocalAnalysis.GLTheoremA.CatB.L62F.fixSub S := fun i hi m hm =>
      CFSG.LocalAnalysis.GLTheoremA.CatB.L62F.fixSub_norm (hIN hi) hm
    rcases no_m3 I eI hd3 hc hU6 (CFSG.LocalAnalysis.GLTheoremA.CatB.L62F.fixSub S) hXd hXI with h | h
    · exact CFSG.LocalAnalysis.GLTheoremA.CatB.L62F.fixSub_ne_bot S hS2 h
    · exact CFSG.LocalAnalysis.GLTheoremA.CatB.L62F.fixSub_ne_top hS h
  ·
    exact (no_m2 I eI hd3 hc (by omega)).elim
  ·
    exact S_analysis I eI hd3 hc (by omega) S hS2 hS (hDN hdD) (fun i hi => hIN hi) j (hcJ j hj)
      (hcJ' j hj)
  ·
    exact absurd (hWtop (Submodule.eq_top_of_finrank_eq (by rw [finrank_Vx]; omega))) hd1

theorem i131L62At_holds {G : Type} [Group G] [Finite G] : I131L62At G :=
  i131L62At_of_core l62Core_holds

end CFSG.LocalAnalysis.GLTheoremA.CatB

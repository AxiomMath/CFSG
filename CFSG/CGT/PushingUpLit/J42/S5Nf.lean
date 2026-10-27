module

public import CFSG.CGT.PushingUpLit.J42.S5P
public import CFSG.CGT.PushingUpLit.J42.S5Model

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.GH74 CFSG.CGT.PushingUpLit.BHS
  CFSG.Quasithin CFSG.Quasithin.G6 Equiv Equiv.Perm

@[expose] def encE (x : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) : Fin 32 :=
  ⟨x.1.1.val + 2 * x.1.2.1.val + 4 * x.1.2.2.val + 8 * x.2.1.val + 16 * x.2.2.val, by
    have h1 := ZMod.val_lt x.1.1
    have h2 := ZMod.val_lt x.1.2.1
    have h3 := ZMod.val_lt x.1.2.2
    have h4 := ZMod.val_lt x.2.1
    have h5 := ZMod.val_lt x.2.2
    omega⟩

@[expose] def decE (i : Fin 32) : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2) :=
  ((((i.val : ℕ) : ZMod 2), ((i.val / 2 : ℕ) : ZMod 2), ((i.val / 4 : ℕ) : ZMod 2)),
    (((i.val / 8 : ℕ) : ZMod 2), ((i.val / 16 : ℕ) : ZMod 2)))

theorem decE_encE : ∀ x : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2), decE (encE x) = x := by
  decide +kernel

theorem encE_decE : ∀ i : Fin 32, encE (decE i) = i := by decide +kernel

@[expose] def mulE (x y : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) :
    (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2) :=
  ((x.1.1 + y.1.1, x.1.2.1 + y.1.2.1, x.1.2.2 + y.1.2.2 + x.2.1 * y.1.2.1 + x.2.2 * y.1.1),
    (x.2.1 + y.2.1, x.2.2 + y.2.2))

theorem extraMulFin_encE : ∀ x y : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2),
    extraMulFin (encE x) (encE y) = encE (mulE x y) := by
  decide +kernel

@[expose] def sigV (a b : ZMod 2) : Perm (Fin 5) := sA ^ a.val * sB ^ b.val

theorem coreAct_sigV : ∀ a b X Y z : ZMod 2,
    coreAct 5 (sigV a b) (qvec X Y z) = qvec X Y (z + a * Y + b * X) := by
  decide +kernel

theorem sigV_inj : ∀ a b a' b' : ZMod 2, sigV a b = sigV a' b' → a = a' ∧ b = b' := by
  decide +kernel

theorem exists_sigV : ∀ σ : Perm (Fin 5), σ ∈ klein → ∃ a b : ZMod 2, σ = sigV a b := by
  decide +kernel

theorem pow_val_mul_pow_val {G : Type*} [Group G] {p : G} (hp : p * p = 1) (a b : ZMod 2) :
    p ^ a.val * p ^ b.val = p ^ (a + b).val := by
  have hp2 : p ^ 2 = 1 := by rw [pow_two]; exact hp
  rw [← pow_add, pow_eq_pow_mod _ hp2, ZMod.val_add]

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : SolCfg G M X 2)

structure SolCfg.Lifts where
  p₁ : G
  p₂ : G
  mem₁ : p₁ ∈ S.PP
  mem₂ : p₂ ∈ S.PP
  hM₁ : p₁ ∈ M
  hM₂ : p₂ ∈ M
  θ₁ : S.θ ⟨p₁, hM₁⟩ = sA
  θ₂ : S.θ ⟨p₂, hM₂⟩ = sB
  sq₁ : p₁ * p₁ = 1
  sq₂ : p₂ * p₂ = 1
  comm : p₁ * p₂ = p₂ * p₁

namespace SolCfg

variable {S}

theorem CaseB.nonempty_lifts (hB : S.CaseB) : Nonempty S.Lifts := by
  obtain ⟨p₁, p₂, h1, h2, hM₁, hM₂, hθ₁, hθ₂, hs₁, hs₂, hc⟩ := hB.exists_lifts
  exact ⟨⟨p₁, p₂, h1, h2, hM₁, hM₂, hθ₁, hθ₂, hs₁, hs₂, hc⟩⟩

namespace Lifts

variable (L : S.Lifts)

@[expose] def vG (a b : ZMod 2) : G := L.p₁ ^ a.val * L.p₂ ^ b.val

theorem vG_mem_PP (a b : ZMod 2) : L.vG a b ∈ S.PP :=
  S.PP.mul_mem (S.PP.pow_mem L.mem₁ _) (S.PP.pow_mem L.mem₂ _)

theorem vG_mem_M (a b : ZMod 2) : L.vG a b ∈ M :=
  M.mul_mem (M.pow_mem L.hM₁ _) (M.pow_mem L.hM₂ _)

theorem vG_mul (a b a' b' : ZMod 2) : L.vG a b * L.vG a' b' = L.vG (a + a') (b + b') := by
  unfold vG
  have hc : Commute (L.p₂ ^ b.val) (L.p₁ ^ a'.val) :=
    (Commute.pow_pow (show Commute L.p₁ L.p₂ from L.comm).symm b.val a'.val)
  calc L.p₁ ^ a.val * L.p₂ ^ b.val * (L.p₁ ^ a'.val * L.p₂ ^ b'.val)
      = L.p₁ ^ a.val * (L.p₂ ^ b.val * L.p₁ ^ a'.val) * L.p₂ ^ b'.val := by
        simp only [mul_assoc]
    _ = L.p₁ ^ a.val * (L.p₁ ^ a'.val * L.p₂ ^ b.val) * L.p₂ ^ b'.val := by rw [hc.eq]
    _ = (L.p₁ ^ a.val * L.p₁ ^ a'.val) * (L.p₂ ^ b.val * L.p₂ ^ b'.val) := by
        simp only [mul_assoc]
    _ = L.p₁ ^ (a + a').val * L.p₂ ^ (b + b').val := by
        rw [pow_val_mul_pow_val L.sq₁, pow_val_mul_pow_val L.sq₂]

theorem θ_vG (a b : ZMod 2) : S.θ ⟨L.vG a b, L.vG_mem_M a b⟩ = sigV a b := by
  have : (⟨L.vG a b, L.vG_mem_M a b⟩ : ↥M) = ⟨L.p₁, L.hM₁⟩ ^ a.val * ⟨L.p₂, L.hM₂⟩ ^ b.val := rfl
  rw [this, map_mul, map_pow, map_pow, L.θ₁, L.θ₂]
  rfl

theorem conj_vG (a b X Y z : ZMod 2) :
    L.vG a b * S.qG X Y z * (L.vG a b)⁻¹ = S.qG X Y (z + a * Y + b * X) :=
  S.conj_qG (L.vG_mem_M a b) (L.θ_vG a b) (coreAct_sigV a b X Y z)

@[expose] noncomputable def nfG (x : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) : G :=
  S.qG x.1.1 x.1.2.1 x.1.2.2 * L.vG x.2.1 x.2.2

theorem nfG_mul (x y : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) :
    L.nfG x * L.nfG y = L.nfG (mulE x y) := by
  obtain ⟨⟨X, Y, z⟩, a, b⟩ := x
  obtain ⟨⟨X', Y', z'⟩, a', b'⟩ := y
  simp only [nfG, mulE]
  have e : S.qG X Y z * L.vG a b * (S.qG X' Y' z' * L.vG a' b') =
      S.qG X Y z * (L.vG a b * S.qG X' Y' z' * (L.vG a b)⁻¹) * (L.vG a b * L.vG a' b') := by
    group
  have h : z + (z' + a * Y' + b * X') = z + z' + a * Y' + b * X' := by ring
  rw [e, L.conj_vG, L.vG_mul, qG_mul, h]

theorem qG_mem_M (X Y z : ZMod 2) : S.qG X Y z ∈ M :=
  pCoreOf_le_self M (S.W_le_Q (S.qG_mem_W X Y z))

theorem θ_qG (X Y z : ZMod 2) : S.θ ⟨S.qG X Y z, qG_mem_M X Y z⟩ = 1 :=
  S.theta_eq_one_of_mem_Q (S.W_le_Q (S.qG_mem_W X Y z))

theorem nfG_mem_M (x : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) : L.nfG x ∈ M :=
  M.mul_mem (qG_mem_M _ _ _) (L.vG_mem_M _ _)

theorem θ_nfG (x : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) :
    S.θ ⟨L.nfG x, L.nfG_mem_M x⟩ = sigV x.2.1 x.2.2 := by
  have : (⟨L.nfG x, L.nfG_mem_M x⟩ : ↥M) =
      ⟨S.qG x.1.1 x.1.2.1 x.1.2.2, qG_mem_M _ _ _⟩ * ⟨L.vG x.2.1 x.2.2, L.vG_mem_M _ _⟩ := rfl
  rw [this, map_mul, θ_qG, L.θ_vG, one_mul]

theorem nfG_inj {x y : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)} (h : L.nfG x = L.nfG y) :
    x = y := by
  have h1 : sigV x.2.1 x.2.2 = sigV y.2.1 y.2.2 := by
    rw [← L.θ_nfG x, ← L.θ_nfG y]
    simp only [h]
  obtain ⟨ha, hb⟩ := sigV_inj _ _ _ _ h1
  have ht : x.2 = y.2 := Prod.ext ha hb
  have h2 : S.qG x.1.1 x.1.2.1 x.1.2.2 = S.qG y.1.1 y.1.2.1 y.1.2.2 := by
    unfold nfG at h
    rw [ha, hb] at h
    exact mul_right_cancel h
  obtain ⟨e1, e2, e3⟩ := S.qG_inj h2
  exact Prod.ext (Prod.ext e1 (Prod.ext e2 e3)) ht

theorem nfG_mem_PP (hB : S.CaseB) (x : (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) :
    L.nfG x ∈ S.PP :=
  S.PP.mul_mem (hB.qG_mem_PP _ _ _) (L.vG_mem_PP _ _)

theorem exists_nfG (hB : S.CaseB) {g : G} (hg : g ∈ S.PP) : ∃ x, g = L.nfG x := by
  have hgM := hB.PP_le_M hg
  obtain ⟨a, b, hab⟩ := exists_sigV _ (hB.theta_mem_klein hg hgM)
  have hvM := L.vG_mem_M a b
  have hqM : g * (L.vG a b)⁻¹ ∈ M := M.mul_mem hgM (M.inv_mem hvM)
  have hθ : S.θ ⟨g * (L.vG a b)⁻¹, hqM⟩ = 1 := by
    have : (⟨g * (L.vG a b)⁻¹, hqM⟩ : ↥M) = ⟨g, hgM⟩ * ⟨L.vG a b, hvM⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hab, L.θ_vG, mul_inv_cancel]
  have hqQ := S.mem_Q_of_theta_eq_one hB.rsmall hqM hθ
  have hqW := S.mem_W_of_rOf_bot hB.rbot hqQ
  have hqP : g * (L.vG a b)⁻¹ ∈ S.PP := S.PP.mul_mem hg (S.PP.inv_mem (L.vG_mem_PP a b))
  obtain ⟨X, Y, z, hq⟩ := hB.exists_qG hqW hqP
  refine ⟨((X, Y, z), (a, b)), ?_⟩
  show g = S.qG X Y z * L.vG a b
  rw [← hq]
  group

end Lifts

theorem x0_ne_one : S.x0 ≠ 1 := by
  rw [S.x0_eq, ← S.qG_zero]
  intro h
  have := (S.qG_inj h).2.2
  revert this
  decide

noncomputable def CaseB.extraData (hB : S.CaseB) (L : S.Lifts) : ExtraData ↥(CGOf S.x0) where
  nf i := ⟨L.nfG (decE i), hB.PP_le_CG (L.nfG_mem_PP hB _)⟩
  nf_inj := fun i j h => by
    have h1 := L.nfG_inj (congrArg Subtype.val h)
    rw [← encE_decE i, ← encE_decE j, h1]
  nf_mul := fun i j => by
    apply Subtype.ext
    show L.nfG (decE i) * L.nfG (decE j) = L.nfG (decE (extraMulFin i j))
    have h : extraMulFin i j = encE (mulE (decE i) (decE j)) := by
      have := extraMulFin_encE (decE i) (decE j)
      rwa [encE_decE, encE_decE] at this
    rw [h, decE_encE, L.nfG_mul]
  nf_conj := fun k i => by
    have hP : (k : G) * L.nfG (decE i) * (k : G)⁻¹ ∈ S.PP :=
      pCoreOf_normalized _ k.2 (L.nfG_mem_PP hB _)
    obtain ⟨x, hx⟩ := L.exists_nfG hB hP
    refine ⟨encE x, Subtype.ext ?_⟩
    show (k : G) * L.nfG (decE i) * (k : G)⁻¹ = L.nfG (decE (encE x))
    rw [decE_encE]
    exact hx
  nf_cent := fun k hk => by
    have hB0 : Subgroup.zpowers S.x0 ≠ ⊥ := by
      simpa [Subgroup.zpowers_eq_bot] using S.x0_ne_one
    have hB2 : IsPGroup 2 (Subgroup.zpowers S.x0) :=
      isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 (S.W_le_Q S.x0_mem_W))
    have hcons := centralizer_two_constrained S.hyp.charTwo hB0 hB2
    have hkP : (k : G) ∈ S.PP := by
      refine hcons ⟨k.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      obtain ⟨x, hx⟩ := L.exists_nfG hB hh
      have := congrArg Subtype.val (hk (encE x))
      have h2 : (k : G) * L.nfG x = L.nfG x * k := by
        simpa [decE_encE] using this
      rw [hx]
      exact h2.symm
    obtain ⟨x, hx⟩ := L.exists_nfG hB hkP
    refine ⟨encE x, Subtype.ext ?_⟩
    show (k : G) = L.nfG (decE (encE x))
    rw [decE_encE]
    exact hx

theorem CaseB.nonempty_extraData (hB : S.CaseB) : Nonempty (ExtraData ↥(CGOf S.x0)) := by
  obtain ⟨L⟩ := hB.nonempty_lifts
  exact ⟨hB.extraData L⟩

end SolCfg

end CFSG.CGT.PushingUpLit.SolK

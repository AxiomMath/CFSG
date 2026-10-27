module

public import CFSG.CGT.Stroth77.Section310CharBCount
public import CFSG.CGT.Stroth77.Section310CharBA

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

namespace StrothWeakTypeData

theorem ofTorus_mem_centralizer_iff (dD : StrothWeakTypeData D τ) {b : G}
    {ψ : Torus τ.k →+ Torus τ.k} (hb : ∀ v, b * dD.ofTorus v = dD.ofTorus (ψ v) * b)
    (v : Torus τ.k) : dD.ofTorus v ∈ Subgroup.centralizer ({b} : Set G) ↔ ψ v = v := by
  rw [Subgroup.mem_centralizer_singleton_iff, hb, mul_left_inj, dD.ofTorus_inj.eq_iff, eq_comm]

theorem card_le_card_filter (dD : StrothWeakTypeData D τ) {H : Subgroup G} (hHD : H ≤ D)
    (P : Torus τ.k → Prop) [DecidablePred P] (hP : ∀ v, dD.ofTorus v ∈ H → P v) :
    Nat.card H ≤ (Finset.univ.filter P).card := by
  classical
  have hv : ∀ x : H, ∃ v, (x : G) = dD.ofTorus v := fun x => dD.exists_ofTorus (hHD x.2)
  choose f hf using hv
  let g : H → {v : Torus τ.k // P v} := fun x => ⟨f x, hP _ (hf x ▸ x.2)⟩
  have hg : Function.Injective g := by
    intro x₁ x₂ h12
    apply Subtype.ext
    rw [hf x₁, hf x₂]
    exact congrArg (fun z : {v // P v} => dD.ofTorus z.1) h12
  calc Nat.card H ≤ Nat.card {v : Torus τ.k // P v} := Nat.card_le_card_of_injective g hg
    _ = (Finset.univ.filter P).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem mul_ofTorus_of_conj (dD : StrothWeakTypeData D τ) {e : G} {φ : Torus τ.k →+ Torus τ.k}
    (hconj : ∀ v, e⁻¹ * dD.ofTorus v * e = dD.ofTorus (φ v)) (hinv : ∀ v, φ (φ v) = v)
    (v : Torus τ.k) : e * dD.ofTorus v = dD.ofTorus (φ v) * e := by
  have h := hconj (φ v)
  rw [hinv] at h
  calc e * dD.ofTorus v = e * (e⁻¹ * dD.ofTorus (φ v) * e) := by rw [h]
    _ = dD.ofTorus (φ v) * e := by group

theorem conj_ofTorus_diag (dD : StrothWeakTypeData D τ) {e : G} {d : Fin 3 → ℤ}
    (hc : e⁻¹ * (dD.c : G) * e = (dD.c : G) ^ d 0) (ha : e⁻¹ * (dD.a : G) * e = (dD.a : G) ^ d 1)
    (hb : e⁻¹ * (dD.b : G) * e = (dD.b : G) ^ d 2) (v : Torus τ.k) :
    e⁻¹ * dD.ofTorus v * e = dD.ofTorus (torusDiag τ.k d v) := by
  refine dD.conj_ofTorus_of_gens ?_ ?_ ?_ v
  · rw [show (Torus.c : Torus τ.k) = gen τ.k 0 from rfl, torusDiag_gen, dD.ofTorus_zsmul]
    exact hc
  · rw [show (Torus.a : Torus τ.k) = gen τ.k 1 from rfl, torusDiag_gen, dD.ofTorus_zsmul]
    exact ha
  · rw [show (Torus.b : Torus τ.k) = gen τ.k 2 from rfl, torusDiag_gen, dD.ofTorus_zsmul]
    exact hb

end StrothWeakTypeData

namespace Stroth310One

@[expose] def diag4 (k : Fin 3 → ℕ) : Fin 4 → (Torus k →+ Torus k) :=
  ![AddMonoidHom.id _, torusDiag k ![1, 5, 5], torusDiag k ![-1, -1, -1], torusDiag k ![-1, 3, 3]]

@[expose] def ActsBy (dD : StrothWeakTypeData D τ) (x : G) (a : Fin 4) : Prop :=
  ∀ v, x * dD.ofTorus v = dD.ofTorus (diag4 τ.k a v) * x

theorem actsBy_of_mem (dD : StrothWeakTypeData D τ) {d : G} (hd : d ∈ D) : ActsBy dD d 0 := by
  intro v
  have hcomm := congrArg Subtype.val
    (dD.isMulCommutative.is_comm.comm ⟨d, hd⟩ ⟨_, dD.ofTorus_mem v⟩)
  simpa [diag4] using hcomm

theorem ActsBy.mul_mem {x d : G} {a : Fin 4} (hx : ActsBy dD x a) (hd : d ∈ D) :
    ActsBy dD (x * d) a := by
  intro v
  have hd' := (actsBy_of_mem dD hd) v
  have h0 : diag4 τ.k 0 v = v := rfl
  rw [h0] at hd'
  rw [mul_assoc, hd', ← mul_assoc, hx v, mul_assoc]

theorem ActsBy.mul {x y : G} {a b c : Fin 4} (hx : ActsBy dD x a) (hy : ActsBy dD y b)
    (habc : ∀ v, diag4 τ.k a (diag4 τ.k b v) = diag4 τ.k c v) : ActsBy dD (x * y) c := by
  intro v
  rw [mul_assoc, hy v, ← mul_assoc, hx, habc, mul_assoc]

theorem actsBy_of_conj (dD : StrothWeakTypeData D τ) {e : G} {a : Fin 4} {d : Fin 3 → ℤ}
    (hd : diag4 τ.k a = torusDiag τ.k d) (hinv : ∀ v, diag4 τ.k a (diag4 τ.k a v) = v)
    (hc : e⁻¹ * (dD.c : G) * e = (dD.c : G) ^ d 0) (ha : e⁻¹ * (dD.a : G) * e = (dD.a : G) ^ d 1)
    (hb : e⁻¹ * (dD.b : G) * e = (dD.b : G) ^ d 2) : ActsBy dD e a :=
  dD.mul_ofTorus_of_conj (fun v => by rw [hd]; exact dD.conj_ofTorus_diag hc ha hb v) hinv

theorem uv_mul_ofTorus_of_actsBy {x : G} {a : Fin 4} (hx : ActsBy dD x a) (v : Torus τ.k) :
    dD.uv * x * dD.ofTorus v =
      dD.ofTorus ((τ.action.φuv.comp (diag4 τ.k a)) v) * (dD.uv * x) := by
  rw [mul_assoc, hx v, ← mul_assoc, dD.uv_mul_ofTorus, mul_assoc]
  rfl

theorem d8_mul_ofTorus_of_actsBy {r : G} {a : Fin 4} (hr : ActsBy dD r a) (i j l : Bool)
    (v : Torus τ.k) :
    dD.d8 i j l * r * dD.ofTorus v =
      dD.ofTorus (((τ.action.d8Act i j l).comp (diag4 τ.k a)) v) * (dD.d8 i j l * r) := by
  rw [mul_assoc, hr v, ← mul_assoc, dD.d8_mul_ofTorus, mul_assoc]
  rfl

theorem card_uv_le {x : G} {a : Fin 4} (hx : ActsBy dD x a) :
    Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G)) ≤
      (Finset.univ.filter fun v => τ.action.φuv (diag4 τ.k a v) = v).card :=
  dD.card_le_card_filter inf_le_left _ fun v hv =>
    (dD.ofTorus_mem_centralizer_iff (uv_mul_ofTorus_of_actsBy hx) v).mp hv.2

theorem card_uv_d8_le {x r : G} {a a' : Fin 4} (hx : ActsBy dD x a) (hr : ActsBy dD r a')
    (i j l : Bool) :
    Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({dD.d8 i j l * r} : Set G)) ≤
      (Finset.univ.filter fun v => τ.action.φuv (diag4 τ.k a v) = v ∧
        τ.action.d8Act i j l (diag4 τ.k a' v) = v).card :=
  dD.card_le_card_filter (inf_le_left.trans inf_le_left) _ fun v hv =>
    ⟨(dD.ofTorus_mem_centralizer_iff (uv_mul_ofTorus_of_actsBy hx) v).mp hv.1.2,
      (dD.ofTorus_mem_centralizer_iff (d8_mul_ofTorus_of_actsBy hr i j l) v).mp hv.2⟩

theorem card_uv_q_le {x q : G} {a b : Fin 4} (hx : ActsBy dD x a) (hq : ActsBy dD q b) :
    Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({q} : Set G)) ≤
      (Finset.univ.filter fun v => τ.action.φuv (diag4 τ.k a v) = v ∧
        diag4 τ.k b v = v).card :=
  dD.card_le_card_filter (inf_le_left.trans inf_le_left) _ fun v hv =>
    ⟨(dD.ofTorus_mem_centralizer_iff (uv_mul_ofTorus_of_actsBy hx) v).mp hv.1.2,
      (dD.ofTorus_mem_centralizer_iff hq v).mp hv.2⟩

end Stroth310One

open Stroth310One

theorem StrothFrame.IsD.mem_normalizer_omegaIn_one (h : F.IsD D dD) (hτ : τ.m ≠ τ.n)
    (hk : ∀ i, 1 ≤ τ.k i) (huvR : ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) → τ.m = τ.n)
    (hD : Nat.card D = 128)
    (F1 : ∀ a : Fin 4, (Finset.univ.filter fun v =>
      τ.action.φuv (diag4 τ.k a v) = v).card ≤ 32)
    (F2 : ∀ a a' : Fin 4, ∀ i j l : Bool, (i, j, l) ≠ (false, false, false) →
      (i, j, l) ≠ (true, false, false) →
      (Finset.univ.filter fun v => τ.action.φuv (diag4 τ.k a v) = v ∧
        τ.action.d8Act i j l (diag4 τ.k a' v) = v).card ≤ 8)
    (F3a : ∀ a : Fin 4, (Finset.univ.filter fun v => τ.action.φuv (diag4 τ.k a v) = v ∧
      diag4 τ.k 1 v = v).card ≤ 16)
    (F3b : ∀ a b : Fin 4, (b = 2 ∨ b = 3) → (Finset.univ.filter fun v =>
      τ.action.φuv (diag4 τ.k a v) = v ∧ diag4 τ.k b v = v).card ≤ 4)
    (hactR : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∃ a, ActsBy dD x a)
    (hQ : ∀ Q : Subgroup G, Q ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) → ¬ Q ≤ D →
      ∃ q ∈ Q, ∃ b : Fin 4, ActsBy dD q b ∧
        ((b = 1 ∧ D.relIndex Q ≤ 2) ∨ ((b = 2 ∨ b = 3) ∧ D.relIndex Q ≤ 4)))
    {g : G}
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  set N : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) with hN
  have huvN : dD.uv ∈ N := ⟨h.uv_eq ▸ F.uv_mem_S, dD.uv_mem⟩
  have htN : dD.t ∈ N := ⟨h.t_eq ▸ F.t_mem_S, dD.t_mem⟩
  have huN : dD.u ∈ N := ⟨h.u_eq ▸ F.u_mem_S, dD.u_mem⟩
  have hclN : Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) ≤ N := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact huvN
    · exact htN
    · exact huN
  have hword : ∀ y ∈ N, (¬ ∀ w ∈ omegaIn 1 D, w * y = y * w) →
      (¬ ∀ w ∈ omegaIn 1 D, w * (dD.uv⁻¹ * y) = dD.uv⁻¹ * y * w) →
      ∃ i j l : Bool, ∃ r : G, ∃ a' : Fin 4, ActsBy dD r a' ∧ y = dD.d8 i j l * r ∧
        (i, j, l) ≠ (false, false, false) ∧ (i, j, l) ≠ (true, false, false) := by
    intro y hy hyC hyC'
    obtain ⟨i, j, l, hijl⟩ := h.exists_d8_inv_mul_mem hk huvR hy
    have hd8N : dD.d8 i j l ∈ N := hclN (dD.d8_mem i j l)
    have hrR : (dD.d8 i j l)⁻¹ * y ∈ N ⊓ Subgroup.centralizer
        ((omegaIn 1 D : Subgroup G) : Set G) :=
      ⟨N.mul_mem (N.inv_mem hd8N) hy, Subgroup.mem_centralizer_iff.mpr fun w hw => hijl w hw⟩
    obtain ⟨a', ha'⟩ := hactR _ hrR
    refine ⟨i, j, l, _, a', ha', by rw [mul_inv_cancel_left], ?_, ?_⟩
    · intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      apply hyC
      intro w hw
      have := hijl w hw
      rwa [dD.d8_fff, inv_one, one_mul] at this
    · intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      apply hyC'
      intro w hw
      have := hijl w hw
      rwa [dD.d8_tff] at this
  have hCQ : ∀ (x : G) (Q : Subgroup G) (q : G), q ∈ Q →
      D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓ Subgroup.centralizer (Q : Set G) ≤
        D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓ Subgroup.centralizer ({q} : Set G) :=
    fun x Q q hq z hz => ⟨hz.1, Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm)⟩
  refine h.mem_normalizer_omegaIn_of_count hτ hk huvR h226 ?_ ?_ ?_ ?_ hgN
  ·
    intro x hx
    obtain ⟨a, ha⟩ := hactR x hx
    have := (card_uv_le ha).trans (F1 a)
    omega
  ·
    intro x hx y hy hyC hyC'
    obtain ⟨a, ha⟩ := hactR x hx
    obtain ⟨i, j, l, r, a', ha', rfl, h1, h2⟩ := hword y hy hyC hyC'
    have := (card_uv_d8_le ha ha' i j l).trans (F2 a a' i j l h1 h2)
    omega
  ·
    intro x hx Q hQR hQD _
    obtain ⟨a, ha⟩ := hactR x hx
    obtain ⟨q, hqQ, b, hq, hb⟩ := hQ Q hQR hQD
    have hc := (Subgroup.card_le_of_le (hCQ x Q q hqQ)).trans (card_uv_q_le ha hq)
    rcases hb with ⟨rfl, hi⟩ | ⟨hb, hi⟩
    · have hX := hc.trans (F3a a)
      calc 2 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
            Subgroup.centralizer (Q : Set G)) ≤ 2 * 2 * 16 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 hi) hX
        _ < Nat.card D := by rw [hD]; norm_num
    · have hX := hc.trans (F3b a b hb)
      calc 2 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
            Subgroup.centralizer (Q : Set G)) ≤ 2 * 4 * 4 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 hi) hX
        _ < Nat.card D := by rw [hD]; norm_num
  ·
    intro x hx Q hQR hQD _ y hy hyC hyC'
    obtain ⟨a, ha⟩ := hactR x hx
    obtain ⟨q, hqQ, b, hq, hb⟩ := hQ Q hQR hQD
    rcases hb with ⟨rfl, hi⟩ | ⟨hb, hi⟩
    · obtain ⟨i, j, l, r, a', ha', rfl, h1, h2⟩ := hword y hy hyC hyC'
      have hle : D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer (Q : Set G) ⊓ Subgroup.centralizer ({dD.d8 i j l * r} : Set G) ≤
          D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
            Subgroup.centralizer ({dD.d8 i j l * r} : Set G) := fun z hz => ⟨hz.1.1, hz.2⟩
      have hX := ((Subgroup.card_le_of_le hle).trans (card_uv_d8_le ha ha' i j l)).trans
        (F2 a a' i j l h1 h2)
      calc 4 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
            Subgroup.centralizer (Q : Set G) ⊓
              Subgroup.centralizer ({dD.d8 i j l * r} : Set G)) ≤ 4 * 2 * 8 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 4 hi) hX
        _ < Nat.card D := by rw [hD]; norm_num
    · have hle : D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer (Q : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ≤
          D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓ Subgroup.centralizer ({q} : Set G) :=
        fun z hz => hCQ x Q q hqQ hz.1
      have hX := ((Subgroup.card_le_of_le hle).trans (card_uv_q_le ha hq)).trans (F3b a b hb)
      calc 4 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
            Subgroup.centralizer (Q : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) ≤ 4 * 4 * 4 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 4 hi) hX
        _ < Nat.card D := by rw [hD]; norm_num

end CFSG.CGT.Stroth77

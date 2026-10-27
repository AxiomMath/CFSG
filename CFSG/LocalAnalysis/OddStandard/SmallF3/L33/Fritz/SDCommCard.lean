module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDKern

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup Equiv CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

@[expose] noncomputable def chat (k' : X) : Subgroup ↥(centralizer ({t} : Set X)) :=
  (Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))).comap ctx.act

private theorem card_comap_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (D : Subgroup H) :
    Nat.card ↥(D.comap f) = Nat.card ↥f.ker * Nat.card ↥D := by
  have h := Subgroup.card_ker_mul_card_of_surjective (f.subgroupComap_surjective D hf)
  have hker : (f.subgroupComap D).ker = f.ker.subgroupOf (D.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  rw [hker, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (MonoidHom.ker_le_comap f D)).toEquiv] at h
  exact h.symm

private theorem card_centralizer_eq_of_isConj {G : Type*} [Group G] {a b : G}
    (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (Subgroup.centralizer ({b} : Set G)) := by
  have horbit : MulAction.orbitRel (ConjAct G) G a b := by
    rw [ConjAct.orbitRel_conjAct]; exact h
  calc Nat.card (Subgroup.centralizer ({a} : Set G))
      = Nat.card (MulAction.stabilizer (ConjAct G) a) :=
        Subgroup.nat_card_centralizer_nat_card_stabilizer a
    _ = Nat.card (MulAction.stabilizer (ConjAct G) b) :=
        Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel horbit).toEquiv
    _ = Nat.card (Subgroup.centralizer ({b} : Set G)) :=
        (Subgroup.nat_card_centralizer_nat_card_stabilizer b).symm

private theorem mulAut_conj_mul (φ : MulAut ↥L) (a : ↥L) :
    φ * MulAut.conj a * φ⁻¹ = MulAut.conj (φ a) := by
  ext u
  simp [MulAut.conj_apply, map_mul, map_inv]

include ctx

private theorem conj_x4_mul_k_sq :
    (MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k) ^ 2 = 1 := by
  have hfix : ctx.M.F.k (ctx.M.F.x ^ 4) = ctx.M.F.x ^ 4 := by
    rw [map_pow, ctx.M.F.k_x]
    have hx5 : ctx.M.F.x * ctx.M.F.x ^ 4 = ctx.M.F.x ^ 5 := by
      rw [show (5 : ℕ) = 1 + 4 by norm_num, pow_add, pow_one]
    rw [hx5, ← pow_mul]
    rw [show (5 * 4 : ℕ) = 8 * 2 + 4 by norm_num, pow_add, pow_mul, ctx.M.F.x_pow_eight,
      one_pow, one_mul]
  have hkca : ctx.M.F.k * MulAut.conj (ctx.M.F.x ^ 4) =
      MulAut.conj (ctx.M.F.k (ctx.M.F.x ^ 4)) * ctx.M.F.k := by
    have h := mulAut_conj_mul ctx.M.F.k (ctx.M.F.x ^ 4)
    calc ctx.M.F.k * MulAut.conj (ctx.M.F.x ^ 4)
        = (ctx.M.F.k * MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k⁻¹) * ctx.M.F.k := by group
      _ = MulAut.conj (ctx.M.F.k (ctx.M.F.x ^ 4)) * ctx.M.F.k := by rw [h]
  have ha2 : (ctx.M.F.x ^ 4) ^ 2 = 1 := by
    rw [← pow_mul, show (4 * 2 : ℕ) = 8 by norm_num, ctx.M.F.x_pow_eight]
  calc (MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k) ^ 2
      = MulAut.conj (ctx.M.F.x ^ 4) * (ctx.M.F.k * MulAut.conj (ctx.M.F.x ^ 4))
          * ctx.M.F.k := by rw [pow_two]; group
    _ = MulAut.conj (ctx.M.F.x ^ 4)
          * (MulAut.conj (ctx.M.F.k (ctx.M.F.x ^ 4)) * ctx.M.F.k) * ctx.M.F.k := by rw [hkca]
    _ = MulAut.conj (ctx.M.F.x ^ 4) * MulAut.conj (ctx.M.F.k (ctx.M.F.x ^ 4))
          * (ctx.M.F.k * ctx.M.F.k) := by group
    _ = MulAut.conj (ctx.M.F.x ^ 4) * MulAut.conj (ctx.M.F.k (ctx.M.F.x ^ 4))
          * ctx.M.F.k ^ 2 := by rw [pow_two]
    _ = MulAut.conj (ctx.M.F.x ^ 4) * MulAut.conj (ctx.M.F.x ^ 4) := by
        rw [hfix, ctx.M.F.k_sq, mul_one]
    _ = 1 := by rw [← map_mul, ← pow_two, ha2, map_one]

private theorem conj_x4_mul_k_outer :
    ¬ ∃ b : ↥L, ∀ u : ↥L,
      (MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k) u = b * u * b⁻¹ := by
  rintro ⟨b, hb⟩
  apply ctx.M.F.k_outer
  refine ⟨(ctx.M.F.x ^ 4)⁻¹ * b, fun u => ?_⟩
  have h := hb u
  rw [MulAut.mul_apply, MulAut.conj_apply] at h
  calc ctx.M.F.k u = (ctx.M.F.x ^ 4)⁻¹ * ((ctx.M.F.x ^ 4) * ctx.M.F.k u
        * (ctx.M.F.x ^ 4)⁻¹) * (ctx.M.F.x ^ 4) := by group
    _ = (ctx.M.F.x ^ 4)⁻¹ * (b * u * b⁻¹) * (ctx.M.F.x ^ 4) := by rw [h]
    _ = ((ctx.M.F.x ^ 4)⁻¹ * b) * u * ((ctx.M.F.x ^ 4)⁻¹ * b)⁻¹ := by group

private theorem actX_zk :
    ctx.actX (ctx.S.z * ctx.C.k) = MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k := by
  have hzC : ctx.S.z ∈ centralizer ({t} : Set X) := ctx.A.T_le_centralizer ctx.S.z_mem.1
  rw [ctx.actX_mul hzC ctx.k_mem_centralizer, ctx.actX_k, ctx.z_eq, ctx.actX_of_mem_L]

private theorem actX_k'_isOuterInv {k' : X}
    (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k) :
    (ctx.actX k') ^ 2 = 1 ∧
      ¬ ∃ b : ↥L, ∀ u : ↥L, ctx.actX k' u = b * u * b⁻¹ := by
  rcases hk' with rfl | rfl
  · exact ⟨by rw [ctx.actX_k]; exact ctx.M.F.k_sq,
      by rw [ctx.actX_k]; exact ctx.M.F.k_outer⟩
  · rw [actX_zk ctx]
    exact ⟨conj_x4_mul_k_sq ctx, conj_x4_mul_k_outer ctx⟩

private theorem card_centralizer_actX {k' : X}
    (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k) :
    Nat.card (Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))) = 48 := by
  obtain ⟨h2, houter⟩ := actX_k'_isOuterInv ctx hk'
  have hconj : IsConj (ctx.actX k') ctx.M.F.k :=
    ctx.M.outer_involutions_conj h2 houter ctx.M.F.k_sq ctx.M.F.k_outer
  rw [card_centralizer_eq_of_isConj hconj, ctx.M.F.card_centralizer_k]

private theorem card_ker_act : Nat.card ↥ctx.act.ker = 2 := by
  have hτker : (⟨t, SD.t_mem_C⟩ : ↥(centralizer ({t} : Set X))) ∈ ctx.act.ker := by
    rw [MonoidHom.mem_ker, ← ctx.actX_of_mem SD.t_mem_C]
    exact (ctx.actX_eq_one_iff SD.t_mem_C).mpr (Or.inr rfl)
  have hker_eq : ctx.act.ker =
      Subgroup.zpowers (⟨t, SD.t_mem_C⟩ : ↥(centralizer ({t} : Set X))) := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr hτker)
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hgX : ctx.actX (g : X) = 1 := by rw [ctx.actX_of_mem g.2]; exact hg
    rcases (ctx.actX_eq_one_iff g.2).mp hgX with h1 | ht
    · rw [show g = 1 from Subtype.ext h1]; exact Subgroup.one_mem _
    · rw [show g = ⟨t, SD.t_mem_C⟩ from Subtype.ext ht]; exact Subgroup.mem_zpowers _
  rw [hker_eq, Nat.card_zpowers, Subgroup.orderOf_mk, ctx.A.orderOf_t]

theorem card_chat {k' : X} (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k) :
    Nat.card ↥(ctx.chat k') = 96 := by
  have hsurj : Function.Surjective ctx.act := by
    intro φ
    obtain ⟨g, hg, hgφ⟩ := ctx.exists_actX_eq φ
    exact ⟨⟨g, hg⟩, by rw [← ctx.actX_of_mem hg]; exact hgφ⟩
  have h := card_comap_of_surjective ctx.act hsurj
    (Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L)))
  simp only [chat]
  rw [h, card_ker_act ctx, card_centralizer_actX ctx hk']

private theorem psi_comm_iff_actX {k' : X} (hk'T : k' ∈ ctx.A.T) {g : X} (hg : g ∈ ctx.A.T) :
    ctx.actX g * ctx.actX k' = ctx.actX k' * ctx.actX g ↔
      ctx.A.ψ ⟨g, hg⟩ * ctx.A.ψ ⟨k', hk'T⟩ =
        ctx.A.ψ ⟨k', hk'T⟩ * ctx.A.ψ ⟨g, hg⟩ := by
  let a : ↥(SDAutP.P ctx.M.F) := ⟨ctx.actX g, ctx.actX_mem_P hg⟩
  let b : ↥(SDAutP.P ctx.M.F) := ⟨ctx.actX k', ctx.actX_mem_P hk'T⟩
  let Φ : ↥(SDAutP.P ctx.M.F) →* Perm (ZMod 8) :=
    H8.subtype.comp (SDAutP.phi ctx.M.F).toMonoidHom
  have h1 : ctx.A.ψ ⟨g, hg⟩ = Φ a := by rw [ctx.ψ_eq hg]; rfl
  have h2 : ctx.A.ψ ⟨k', hk'T⟩ = Φ b := by rw [ctx.ψ_eq hk'T]; rfl
  rw [h1, h2]
  constructor
  · intro h
    have h1 : a * b = b * a := Subtype.ext h
    have h2 : Φ a * Φ b = Φ b * Φ a := by
      rw [← map_mul, ← map_mul]
      exact congrArg Φ h1
    exact h2
  · intro h
    have h' : (SDAutP.phi ctx.M.F) (a * b) = (SDAutP.phi ctx.M.F) (b * a) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h
    have h'' : a * b = b * a := by
      simpa using congrArg (SDAutP.phi ctx.M.F).symm h'
    exact congrArg Subtype.val h''

private theorem range_psi_eq_H8 : ctx.A.ψ.range = H8 := by
  refine SD.eq_H8_of_S16_le_of_k8_mem ctx.A.range_le_H8 ctx.A.S16_le_range ?_
  exact ⟨⟨ctx.C.k, ctx.C.k_mem⟩, ctx.C.ψ_k⟩

private theorem card_ker_psi : Nat.card ↥ctx.A.ψ.ker = 2 := by
  have hker : ctx.A.ψ.ker = ctx.A.K.subgroupOf ctx.A.T := by
    ext g
    rw [MonoidHom.mem_ker, ctx.A.ψ_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  rw [hker, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : ctx.A.K ≤ ctx.A.T)).toEquiv,
    ctx.C.card_K]

private theorem card_cent_psi_range {k' : X}
    (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k) (hk'T : k' ∈ ctx.A.T) :
    Nat.card ↥(Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} : Set (Perm (ZMod 8))) ⊓
      ctx.A.ψ.range) = 16 := by
  rw [range_psi_eq_H8 ctx]
  rcases hk' with rfl | rfl
  · rw [show (⟨ctx.C.k, hk'T⟩ : ↥ctx.A.T) = ⟨ctx.C.k, ctx.C.k_mem⟩ from Subtype.ext rfl,
      ctx.C.ψ_k, inf_comm]
    exact SD.card_H8_inf_centralizer_k8
  · have hψzk : ctx.A.ψ ⟨ctx.S.z * ctx.C.k, hk'T⟩ = z8 * k8 := by
      rw [show (⟨ctx.S.z * ctx.C.k, hk'T⟩ : ↥ctx.A.T) =
          ⟨ctx.S.z, ctx.S.z_mem.1⟩ * ⟨ctx.C.k, ctx.C.k_mem⟩ from Subtype.ext rfl, map_mul]
      rw [← SD.ψX_of_mem (A := ctx.A) (g := ctx.S.z) ctx.S.z_mem.1, ctx.S.ψ_z, ctx.C.ψ_k]
    rw [hψzk, inf_comm]
    have hsub : H8 ⊓ Subgroup.centralizer ({z8 * k8} : Set (Perm (ZMod 8))) =
        H8 ⊓ Subgroup.centralizer ({k8} : Set (Perm (ZMod 8))) := by
      ext σ
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => ⟨h.1, (SD.commute_z8_mul_k8_iff h.1).mp h.2⟩,
        fun h => ⟨h.1, (SD.commute_z8_mul_k8_iff h.1).mpr h.2⟩⟩
    rw [hsub]
    exact SD.card_H8_inf_centralizer_k8

private theorem card_inf_chat_eq_comap_psi {k' : X}
    (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k) (hk'T : k' ∈ ctx.A.T) :
    Nat.card ↥((ctx.A.syl : Subgroup ↥(centralizer ({t} : Set X))) ⊓ ctx.chat k') =
      Nat.card ↥((Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} : Set (Perm (ZMod 8)))).comap
        ctx.A.ψ) := by
  let S : Subgroup ↥(centralizer ({t} : Set X)) := (ctx.A.syl : Subgroup _)
  let e : ↥S ≃* ↥(ctx.A.T) :=
    Subgroup.equivMapOfInjective S (centralizer ({t} : Set X)).subtype (subtype_injective _)
  have heq : (((Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))).comap
        ctx.act).subgroupOf S).map e.toMonoidHom =
      (Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} : Set (Perm (ZMod 8)))).comap ctx.A.ψ := by
    ext y
    have hiff : y ∈ ((((Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))).comap
        ctx.act).subgroupOf S).map e.toMonoidHom) ↔
        e.symm y ∈ ((Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))).comap
          ctx.act).subgroupOf S := by
      constructor
      · rintro ⟨z, hz, hzy⟩
        have hzy' : e.symm y = z := by
          rw [← hzy]
          exact MulEquiv.symm_apply_apply e z
        rwa [hzy']
      · intro h
        exact ⟨e.symm y, h, by simp⟩
    rw [hiff, Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_comap,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have hxy : (((e.symm y : ↥S) : ↥(centralizer ({t} : Set X))) : X) = (y : X) :=
      congrArg (fun w : ↥(ctx.A.T) => (w : X)) (MulEquiv.apply_symm_apply e y)
    have hact : ctx.act (e.symm y) = ctx.actX (y : X) := by
      rw [← ctx.actX_of_mem (((e.symm y : ↥S) : ↥(centralizer ({t} : Set X))).2), hxy]
    rw [hact]
    exact psi_comm_iff_actX ctx hk'T y.2
  calc Nat.card ↥(S ⊓ ctx.chat k')
      = Nat.card ↥(((Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))).comap
          ctx.act).subgroupOf S) := by
        have hsub : (S ⊓ (Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))).comap
              ctx.act).subgroupOf S =
            ((Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))).comap
              ctx.act).subgroupOf S := by
          ext x
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
          exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
        simp only [chat]
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : S ⊓ (Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))).comap
            ctx.act ≤ S)).toEquiv, hsub]
    _ = Nat.card ↥((((Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L))).comap
          ctx.act).subgroupOf S).map e.toMonoidHom) :=
        Nat.card_congr (e.subgroupMap _).toEquiv
    _ = Nat.card ↥((Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} : Set (Perm (ZMod 8)))).comap
          ctx.A.ψ) := by rw [heq]

theorem card_T_inf_chat {k' : X} (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k) :
    Nat.card ↥((ctx.A.syl : Subgroup ↥(centralizer ({t} : Set X))) ⊓ ctx.chat k') = 32 := by
  have hk'T : k' ∈ ctx.A.T := by
    rcases hk' with rfl | rfl
    · exact ctx.C.k_mem
    · exact ctx.A.T.mul_mem ctx.S.z_mem.1 ctx.C.k_mem
  rw [card_inf_chat_eq_comap_psi ctx hk' hk'T]
  have hcard : Nat.card ↥((Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} :
        Set (Perm (ZMod 8)))).comap ctx.A.ψ) = Nat.card ↥ctx.A.ψ.ker *
      Nat.card ↥(Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} : Set (Perm (ZMod 8))) ⊓
        ctx.A.ψ.range) := by
    have h := card_comap_of_surjective ctx.A.ψ.rangeRestrict
      ctx.A.ψ.rangeRestrict_surjective
      ((Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} : Set (Perm (ZMod 8))) ⊓
        ctx.A.ψ.range).subgroupOf ctx.A.ψ.range)
    have heq1 : ((Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} : Set (Perm (ZMod 8))) ⊓
          ctx.A.ψ.range).subgroupOf ctx.A.ψ.range).comap ctx.A.ψ.rangeRestrict =
        (Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} : Set (Perm (ZMod 8)))).comap
          ctx.A.ψ := by
      ext x
      rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, (ctx.A.ψ.rangeRestrict x).2⟩⟩
    have heq2 : ctx.A.ψ.rangeRestrict.ker = ctx.A.ψ.ker := by
      ext x
      simp [MonoidHom.mem_ker]
    have hcard' : Nat.card ↥(((Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} :
          Set (Perm (ZMod 8))) ⊓ ctx.A.ψ.range).subgroupOf ctx.A.ψ.range)) =
        Nat.card ↥(Subgroup.centralizer ({ctx.A.ψ ⟨k', hk'T⟩} : Set (Perm (ZMod 8))) ⊓
          ctx.A.ψ.range) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : _ ⊓ ctx.A.ψ.range ≤ ctx.A.ψ.range)).toEquiv
    rw [heq1, heq2, hcard'] at h
    exact h
  rw [hcard, card_ker_psi ctx, card_cent_psi_range ctx hk' hk'T]

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx

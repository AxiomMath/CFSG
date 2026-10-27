module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Seven
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem isElemAbelian_map_conj {X : Subgroup G} (hX : CFSG.Open.IsElemAbelian 2 X) (g : G) :
    CFSG.Open.IsElemAbelian 2 (X.map (MulAut.conj g).toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hX _

theorem Hyp.fusion_A_B
    (hd : d.Hyp) {D : Subgroup G} (hD : D = d.A ∨ D = d.B) {g : G}
    (hg : D.map (MulAut.conj g).toMonoidHom ≤ centralizer ({d.t} : Set G)) :
    ∃ h ∈ centralizer ({d.t} : Set G),
      D.map (MulAut.conj h).toMonoidHom = D.map (MulAut.conj g).toMonoidHom := by
  have hDa : CFSG.Open.IsElemAbelian 2 D ∧ Nat.card D = 2 ^ 6 := by
    rcases hD with rfl | rfl
    · exact ⟨hd.A_facts.2.2.1, hd.A_facts.2.2.2.1⟩
    · exact ⟨hd.B_facts.2.2.1, hd.B_facts.2.2.2.1⟩
  obtain ⟨c, hc, hY⟩ := hd.exists_map_conj_eq_A_or_B hg (isElemAbelian_map_conj hDa.1 g)
    (by rw [Model.card_map_conj, hDa.2])
  rw [Model.map_conj_map_conj] at hY
  have back : ∀ {X : Subgroup G}, D.map (MulAut.conj (c * g)).toMonoidHom = X →
      X.map (MulAut.conj c⁻¹).toMonoidHom = D.map (MulAut.conj g).toMonoidHom := by
    intro X hX
    rw [← hX, Model.map_conj_map_conj, show c⁻¹ * (c * g) = g by group]
  rcases hD with rfl | rfl
  · rcases hY with h | h
    · exact ⟨c⁻¹, inv_mem hc, back h⟩
    · exact absurd h (hd.map_conj_A_ne_B_of_G (c * g))
  · rcases hY with h | h
    · exfalso
      apply hd.map_conj_A_ne_B_of_G (c * g)⁻¹
      rw [← h, Model.map_conj_map_conj, inv_mul_cancel, Model.map_conj_one]
    · exact ⟨c⁻¹, inv_mem hc, back h⟩

theorem Hyp.transitive
    (hd : d.Hyp) {D : Subgroup G} (hD : D = d.A ∨ D = d.B) {s : G} (hs : s ∈ d.tG)
    (hsD : s ∈ D) : ∃ n ∈ normalizer (D : Set G), n * d.t * n⁻¹ = s := by
  obtain ⟨g, rfl⟩ := hs
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    rcases hD with rfl | rfl
    · exact fun a ha b hb => congrArg Subtype.val
        (hd.A_facts.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · exact fun a ha b hb => congrArg Subtype.val
        (hd.B_facts.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact manning_conj_normalizer (fun g' hg' => hd.fusion_A_B hD hg')
    (fun x hx => mem_centralizer_singleton_iff.2 (hcomm x hx _ hsD))

theorem Hyp.A_inf_L
    (hd : d.Hyp) : d.A ⊓ d.L = d.E :=
  le_antisymm (fun x hx => hd.A_facts.2.2.2.2 x (mem_inf.1 hx).1 (mem_inf.1 hx).2)
    (le_inf le_sup_left (d.liftSub_le _))

theorem Hyp.B_inf_L
    (hd : d.Hyp) : d.B ⊓ d.L = d.F :=
  le_antisymm (fun x hx => hd.B_facts.2.2.2.2 x (mem_inf.1 hx).1 (mem_inf.1 hx).2)
    (le_inf le_sup_left (d.liftSub_le _))

theorem Hyp.conj_mem_of_t_mul_mem_tG
    (hd : d.Hyp) {X : Subgroup (Equiv.Perm (Fin 1755))} {n : G}
    (hn : n ∈ normalizer ((d.liftSub X ⊔ zpowers d.t : Subgroup G) : Set G)) {u : G}
    (hu : u ∈ d.liftSub X) (htu : d.t * u ∈ d.tG) : n * u * n⁻¹ ∈ d.liftSub X := by
  have hPL := d.liftSub_le X
  have htD : d.t ∈ d.liftSub X ⊔ zpowers d.t := mem_sup_right (mem_zpowers _)
  have htuD : d.t * u ∈ d.liftSub X ⊔ zpowers d.t := mul_mem htD (mem_sup_left hu)
  have h1 := hd.t_mul_mem_of_mem_tG hPL (s := n * d.t * n⁻¹) ⟨n, rfl⟩
    ((mem_normalizer_iff.1 hn _).1 htD)
  have h2 := hd.t_mul_mem_of_mem_tG hPL (s := n * (d.t * u) * n⁻¹)
    (by obtain ⟨g, hg⟩ := htu; exact ⟨n * g, by rw [← hg]; group⟩)
    ((mem_normalizer_iff.1 hn _).1 htuD)
  have e : n * u * n⁻¹ = (d.t * (n * d.t * n⁻¹))⁻¹ * (d.t * (n * (d.t * u) * n⁻¹)) := by group
  rw [e]
  exact mul_mem (inv_mem h1) h2

theorem Hyp.M_le_normalizer
    (hd : d.Hyp) : d.M ≤ normalizer ((d.A ⊓ d.L : Subgroup G) : Set G) := by
  rw [hd.A_inf_L]
  intro n hn
  apply CFSG.Quasithin.mem_normalizer_of_forall_conj_mem_f4
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  have hlong : ∀ u ∈ d.E, u ∈ d.zL → n * u * n⁻¹ ∈ d.E := fun u hu hz =>
    hd.conj_mem_of_t_mul_mem_tG hn hu (hd.t_mul_mem_tG_of_zL hz)
  intro e he
  by_cases he1 : e = 1
  · rw [he1, mul_one, mul_inv_cancel]
    exact one_mem _
  rcases d.mem_zL_or_vL (fun x hx hx1 => Model.hatE_long_or_short hx hx1) he he1 with hz | hv
  · exact hlong e he hz
  · obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 he
    have hxs : Model.IsShort x := by
      rw [vL_eq] at hv
      obtain ⟨y, ⟨hyD, hys⟩, hyx⟩ := hv
      rwa [← d.lift_inj hyD hxD hyx]
    obtain ⟨x₁, hx₁, x₂, hx₂, hl₁, hl₂, rfl⟩ := Model.hatE_short_mul hx hxs
    rw [d.lift_mul (hED hx₁) (hED hx₂)]
    have hz₁ : d.lift x₁ ∈ d.zL := by rw [zL_eq]; exact ⟨x₁, ⟨hED hx₁, hl₁⟩, rfl⟩
    have hz₂ : d.lift x₂ ∈ d.zL := by rw [zL_eq]; exact ⟨x₂, ⟨hED hx₂, hl₂⟩, rfl⟩
    have e : n * (d.lift x₁ * d.lift x₂) * n⁻¹ =
        (n * d.lift x₁ * n⁻¹) * (n * d.lift x₂ * n⁻¹) := by group
    rw [e]
    exact mul_mem (hlong _ (mem_liftSub.2 ⟨x₁, hx₁, hED hx₁, rfl⟩) hz₁)
      (hlong _ (mem_liftSub.2 ⟨x₂, hx₂, hED hx₂, rfl⟩) hz₂)

theorem Hyp.conj_inv_mem_L_of_mem_F
    (hd : d.Hyp) {k : G} (hk : k * d.t * k⁻¹ = d.t * d.z) {f : G} (hf : f ∈ d.F) :
    k⁻¹ * f * k ∈ d.L := by
  obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 hf
  have hcomm : ∀ a ∈ titsH, k⁻¹ * d.lift a * k ∈ centralizer ({d.t} : Set G) := by
    intro a ha
    have haD : a ∈ titsD := titsH_le_titsD ha
    have haz : a * titsZ = titsZ * a :=
      mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z ha)
    have h1 : d.lift a * d.z = d.z * d.lift a := by
      rw [← d.lift_titsZ]
      exact d.lift_comm haD titsZ_mem_titsD haz
    have h2 : d.lift a * d.t = d.t * d.lift a := hd.L_comm_t (d.lift_mem a)
    have hc : d.lift a * (d.t * d.z) = (d.t * d.z) * d.lift a := by
      rw [← mul_assoc, h2, mul_assoc, h1, ← mul_assoc]
    rw [mem_centralizer_singleton_iff]
    have hkt : d.t = k⁻¹ * (d.t * d.z) * k := by rw [← hk]; group
    calc k⁻¹ * d.lift a * k * d.t = k⁻¹ * (d.lift a * (d.t * d.z)) * k := by
          conv_lhs => rw [hkt]
          group
      _ = k⁻¹ * ((d.t * d.z) * d.lift a) * k := by rw [hc]
      _ = d.t * (k⁻¹ * d.lift a * k) := by
          conv_rhs => rw [hkt]
          group
  have hFD : Model.parrottF ≤ titsD := Model.parrottF_le_titsD
  clear hf hxD
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨a, ha, b, hb, hab⟩ := Model.parrottV_eq_comm hi
    have haD := titsH_le_titsD ha
    have hbD := titsH_le_titsD hb
    have hc := hd.commutator_mem (hcomm a ha) (hcomm b hb)
    rw [← hab, d.lift_mul (mul_mem (mul_mem haD hbD) (inv_mem haD)) (inv_mem hbD),
      d.lift_mul (mul_mem haD hbD) (inv_mem haD), d.lift_mul haD hbD, d.lift_inv haD,
      d.lift_inv hbD]
    have e : k⁻¹ * (d.lift a * d.lift b * (d.lift a)⁻¹ * (d.lift b)⁻¹) * k =
        ⁅k⁻¹ * d.lift a * k, k⁻¹ * d.lift b * k⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact hc
  | one =>
    rw [d.lift_one, mul_one, inv_mul_cancel]
    exact one_mem _
  | mul y w hy hw ihy ihw =>
    rw [d.lift_mul (hFD hy) (hFD hw)]
    have e : k⁻¹ * (d.lift y * d.lift w) * k = (k⁻¹ * d.lift y * k) * (k⁻¹ * d.lift w * k) := by
      group
    rw [e]
    exact mul_mem ihy ihw
  | inv y hy ihy =>
    rw [d.lift_inv (hFD hy)]
    have e : k⁻¹ * (d.lift y)⁻¹ * k = (k⁻¹ * d.lift y * k)⁻¹ := by group
    rw [e]
    exact inv_mem ihy

theorem Hyp.N_le_normalizer
    (hd : d.Hyp) : d.N ≤ normalizer ((d.B ⊓ d.L : Subgroup G) : Set G) := by
  rw [hd.B_inf_L]
  intro n hn
  apply CFSG.Quasithin.mem_normalizer_of_forall_conj_mem_f4
  have ht2 := hd.t_mul_self
  have hF : ∀ x ∈ Model.parrottF, x ≠ 1 → Model.IsLong x ∨ Model.IsShort x :=
    fun x hx hx1 => Model.parrottF_long_or_short hx hx1
  have hCN : ∀ c ∈ d.N, c ∈ centralizer ({d.t} : Set G) → ∀ f ∈ d.F, c * f * c⁻¹ ∈ d.F := by
    intro c hcN hcC f hf
    refine hd.B_facts.2.2.2.2 _ ((mem_normalizer_iff.1 hcN f).1 (mem_sup_left hf)) ?_
    exact hd.conj_mem ⟨c, hcC⟩ (d.liftSub_le _ hf)
  by_cases hτ : d.t * d.v ∈ d.tG
  · intro f hf
    by_cases hf1 : f = 1
    · rw [hf1, mul_one, mul_inv_cancel]
      exact one_mem _
    have htf : d.t * f ∈ d.tG := by
      rcases d.mem_zL_or_vL hF hf hf1 with hz | hv
      · exact hd.t_mul_mem_tG_of_zL hz
      · exact (hd.t_mul_mem_tG_iff_of_vL hv).2 hτ
    exact hd.conj_mem_of_t_mul_mem_tG hn hf htf
  · have hs : n * d.t * n⁻¹ ∈ d.tG := ⟨n, rfl⟩
    have hsB : n * d.t * n⁻¹ ∈ d.B :=
      (mem_normalizer_iff.1 hn _).1 (mem_sup_right (mem_zpowers _))
    have he := hd.t_mul_mem_of_mem_tG (d.liftSub_le _) hs hsB
    have hnts : n * d.t * n⁻¹ = d.t * (d.t * (n * d.t * n⁻¹)) := by
      rw [← mul_assoc, ht2, one_mul]
    by_cases he1 : d.t * (n * d.t * n⁻¹) = 1
    · have hnt : n * d.t * n⁻¹ = d.t := by rw [hnts, he1, mul_one]
      have hnC : n ∈ centralizer ({d.t} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        calc n * d.t = n * d.t * n⁻¹ * n := by group
          _ = d.t * n := by rw [hnt]
      exact hCN n hn hnC
    rcases d.mem_zL_or_vL hF he he1 with hz | hv
    · have heB : d.t * (n * d.t * n⁻¹) ∈ d.zL ∩ d.B := ⟨hz, mem_sup_left he⟩
      rw [← hd.orbits_B.1] at heB
      obtain ⟨c, hc, hce⟩ := heB
      obtain ⟨hcN, hcC⟩ := mem_inf.1 hc
      have hkN : c⁻¹ * n ∈ d.N := mul_mem (inv_mem hcN) hn
      have hkt : c⁻¹ * n * d.t * (c⁻¹ * n)⁻¹ = d.t * d.z := by
        have hct : c * d.t = d.t * c := mem_centralizer_singleton_iff.1 hcC
        have h1 : n * d.t * n⁻¹ = d.t * (c * d.z * c⁻¹) := by rw [hce, ← hnts]
        calc c⁻¹ * n * d.t * (c⁻¹ * n)⁻¹ = c⁻¹ * (n * d.t * n⁻¹) * c := by group
          _ = c⁻¹ * (d.t * (c * d.z * c⁻¹)) * c := by rw [h1]
          _ = c⁻¹ * (d.t * c) * d.z := by group
          _ = c⁻¹ * (c * d.t) * d.z := by rw [hct]
          _ = d.t * d.z := by group
      have hk1 : (c⁻¹ * n)⁻¹ ∈ normalizer (d.F : Set G) := by
        apply CFSG.Quasithin.mem_normalizer_of_forall_conj_mem_f4
        intro f hf
        have hL := hd.conj_inv_mem_L_of_mem_F hkt hf
        have hB : (c⁻¹ * n)⁻¹ * f * (c⁻¹ * n) ∈ d.B := by
          have := (mem_normalizer_iff.1 (inv_mem hkN) f).1 (mem_sup_left hf)
          simpa using this
        rw [inv_inv]
        exact hd.B_facts.2.2.2.2 _ hB hL
      have hk : c⁻¹ * n ∈ normalizer (d.F : Set G) := by simpa using inv_mem hk1
      intro f hf
      have e' : n * f * n⁻¹ = c * ((c⁻¹ * n) * f * (c⁻¹ * n)⁻¹) * c⁻¹ := by group
      rw [e']
      exact hCN c hcN hcC _ ((mem_normalizer_iff.1 hk f).1 hf)
    · exfalso
      apply hτ
      rw [← hd.t_mul_mem_tG_iff_of_vL hv, ← hnts]
      exact hs

theorem Hyp.thm47_two
    (hd : d.Hyp) {D : Subgroup G} (hD : D = d.A ∨ D = d.B) :
    (∀ s ∈ d.tG ∩ D, d.t * s ∈ D ⊓ d.L) ∧
      (∀ s ∈ d.tG ∩ D, ∃ n ∈ normalizer (D : Set G), n * d.t * n⁻¹ = s) ∧
      normalizer (D : Set G) ≤ normalizer ((D ⊓ d.L : Subgroup G) : Set G) := by
  refine ⟨fun s hs => ?_, fun s hs => hd.transitive hD hs.1 hs.2, ?_⟩
  · rcases hD with rfl | rfl
    · have h := hd.t_mul_mem_of_mem_tG (d.liftSub_le _) hs.1 hs.2
      exact mem_inf.2 ⟨mem_sup_left h, d.liftSub_le _ h⟩
    · have h := hd.t_mul_mem_of_mem_tG (d.liftSub_le _) hs.1 hs.2
      exact mem_inf.2 ⟨mem_sup_left h, d.liftSub_le _ h⟩
  · rcases hD with rfl | rfl
    · exact hd.M_le_normalizer
    · exact hd.N_le_normalizer

end Data

end CFSG.LocalAnalysis.EvenBN.Tits

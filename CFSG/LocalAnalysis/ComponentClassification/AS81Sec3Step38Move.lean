module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Img

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

section Rotation

variable {G : Type} [Group G]

theorem comm_mem_of_rotation {V K : Subgroup G} {x s v₀ : G} (hx3 : x * x * x = 1)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hxK' : ∀ k ∈ K, x⁻¹ * k * x ∈ K)
    (hsK : ∀ k ∈ K, s * k * s⁻¹ ∈ K) (hsV : ∀ w ∈ V, s * w * s⁻¹ ∈ V) (hsx : s * x = x * s)
    (hs2 : ∀ w ∈ V, s * (s * w * s⁻¹) * s⁻¹ = w) (hv₀ : v₀ ∈ V) (h0 : v₀ ∉ K)
    (h1 : v₀ * (x * v₀ * x⁻¹)⁻¹ ∉ K) (h2 : v₀ * (x⁻¹ * v₀ * x)⁻¹ ∉ K)
    (hcover : ∀ w ∈ V, w ∈ K ∨ w * v₀⁻¹ ∈ K ∨ w * (x * v₀ * x⁻¹)⁻¹ ∈ K ∨
      w * (x⁻¹ * v₀ * x)⁻¹ ∈ K) :
    ∀ w ∈ V, s * w * s⁻¹ * w⁻¹ ∈ K := by
  have hxinv : x⁻¹ = x * x := by
    calc x⁻¹ = x⁻¹ * (x * x * x) := by rw [hx3, mul_one]
      _ = x * x := by group
  have hcomm : ∀ {a : G}, s * a = a * s →
      ∀ w : G, s * (a * w * a⁻¹) * s⁻¹ = a * (s * w * s⁻¹) * a⁻¹ := by
    intro a ha w
    calc s * (a * w * a⁻¹) * s⁻¹ = (s * a) * w * (s * a)⁻¹ := by group
      _ = (a * s) * w * (a * s)⁻¹ := by rw [ha]
      _ = a * (s * w * s⁻¹) * a⁻¹ := by group
  have hsx' : s * x⁻¹ = x⁻¹ * s := by
    calc s * x⁻¹ = x⁻¹ * (x * s) * x⁻¹ := by group
      _ = x⁻¹ * (s * x) * x⁻¹ := by rw [hsx]
      _ = x⁻¹ * s := by group
  have hcomm' : ∀ w : G, s * (x⁻¹ * w * x) * s⁻¹ = x⁻¹ * (s * w * s⁻¹) * x := fun w => by
    have h := hcomm hsx' w
    rwa [inv_inv] at h
  have e12 : x * (x * v₀ * x⁻¹) * x⁻¹ = x⁻¹ * v₀ * x := by
    rw [show x * (x * v₀ * x⁻¹) * x⁻¹ = (x * x) * v₀ * (x * x)⁻¹ by group, ← hxinv, inv_inv]
  have e21 : x⁻¹ * (x⁻¹ * v₀ * x) * x = x * v₀ * x⁻¹ := by
    rw [show x⁻¹ * (x⁻¹ * v₀ * x) * x = (x * x)⁻¹ * v₀ * (x * x) by group, ← hxinv, inv_inv]
  have hσ0 : s * v₀ * s⁻¹ ∉ K := by
    intro h
    apply h0
    have h' := hsK _ h
    rwa [hs2 v₀ hv₀] at h'
  have hk0 : s * v₀ * s⁻¹ * v₀⁻¹ ∈ K := by
    rcases hcover _ (hsV v₀ hv₀) with h | h | h | h
    · exact absurd h hσ0
    · exact h
    · exfalso
      apply h2
      obtain ⟨k, hkK, hkdef⟩ : ∃ k ∈ K, s * v₀ * s⁻¹ = k * (x * v₀ * x⁻¹) := ⟨_, h, by group⟩
      have e1 : s * (x * v₀ * x⁻¹) * s⁻¹ = (x * k * x⁻¹) * (x⁻¹ * v₀ * x) := by
        rw [hcomm hsx v₀, hkdef, ← e12]
        group
      have e2 : v₀ = (s * k * s⁻¹) * (x * k * x⁻¹) * (x⁻¹ * v₀ * x) := by
        calc v₀ = s * (s * v₀ * s⁻¹) * s⁻¹ := (hs2 v₀ hv₀).symm
          _ = s * (k * (x * v₀ * x⁻¹)) * s⁻¹ := by rw [hkdef]
          _ = (s * k * s⁻¹) * (s * (x * v₀ * x⁻¹) * s⁻¹) := by group
          _ = (s * k * s⁻¹) * ((x * k * x⁻¹) * (x⁻¹ * v₀ * x)) := by rw [e1]
          _ = (s * k * s⁻¹) * (x * k * x⁻¹) * (x⁻¹ * v₀ * x) := by group
      have e3 : v₀ * (x⁻¹ * v₀ * x)⁻¹ = (s * k * s⁻¹) * (x * k * x⁻¹) := by
        calc v₀ * (x⁻¹ * v₀ * x)⁻¹ =
            (s * k * s⁻¹) * (x * k * x⁻¹) * (x⁻¹ * v₀ * x) * (x⁻¹ * v₀ * x)⁻¹ := by
              rw [← e2]
          _ = (s * k * s⁻¹) * (x * k * x⁻¹) := by group
      rw [e3]
      exact mul_mem (hsK k hkK) (hxK k hkK)
    · exfalso
      apply h1
      obtain ⟨k, hkK, hkdef⟩ : ∃ k ∈ K, s * v₀ * s⁻¹ = k * (x⁻¹ * v₀ * x) := ⟨_, h, by group⟩
      have e1 : s * (x⁻¹ * v₀ * x) * s⁻¹ = (x⁻¹ * k * x) * (x * v₀ * x⁻¹) := by
        rw [hcomm' v₀, hkdef, ← e21]
        group
      have e2 : v₀ = (s * k * s⁻¹) * (x⁻¹ * k * x) * (x * v₀ * x⁻¹) := by
        calc v₀ = s * (s * v₀ * s⁻¹) * s⁻¹ := (hs2 v₀ hv₀).symm
          _ = s * (k * (x⁻¹ * v₀ * x)) * s⁻¹ := by rw [hkdef]
          _ = (s * k * s⁻¹) * (s * (x⁻¹ * v₀ * x) * s⁻¹) := by group
          _ = (s * k * s⁻¹) * ((x⁻¹ * k * x) * (x * v₀ * x⁻¹)) := by rw [e1]
          _ = (s * k * s⁻¹) * (x⁻¹ * k * x) * (x * v₀ * x⁻¹) := by group
      have e3 : v₀ * (x * v₀ * x⁻¹)⁻¹ = (s * k * s⁻¹) * (x⁻¹ * k * x) := by
        calc v₀ * (x * v₀ * x⁻¹)⁻¹ =
            (s * k * s⁻¹) * (x⁻¹ * k * x) * (x * v₀ * x⁻¹) * (x * v₀ * x⁻¹)⁻¹ := by
              rw [← e2]
          _ = (s * k * s⁻¹) * (x⁻¹ * k * x) := by group
      rw [e3]
      exact mul_mem (hsK k hkK) (hxK' k hkK)
  have hk1 : s * (x * v₀ * x⁻¹) * s⁻¹ * (x * v₀ * x⁻¹)⁻¹ ∈ K := by
    rw [hcomm hsx v₀, show x * (s * v₀ * s⁻¹) * x⁻¹ * (x * v₀ * x⁻¹)⁻¹ =
      x * (s * v₀ * s⁻¹ * v₀⁻¹) * x⁻¹ by group]
    exact hxK _ hk0
  have hk2 : s * (x⁻¹ * v₀ * x) * s⁻¹ * (x⁻¹ * v₀ * x)⁻¹ ∈ K := by
    rw [hcomm' v₀, show x⁻¹ * (s * v₀ * s⁻¹) * x * (x⁻¹ * v₀ * x)⁻¹ =
      x⁻¹ * (s * v₀ * s⁻¹ * v₀⁻¹) * x by group]
    exact hxK' _ hk0
  have hgen : ∀ {w v : G}, w * v⁻¹ ∈ K → s * v * s⁻¹ * v⁻¹ ∈ K → s * w * s⁻¹ * w⁻¹ ∈ K := by
    intro w v hw hv
    have e : s * w * s⁻¹ * w⁻¹ =
        (s * (w * v⁻¹) * s⁻¹) * (s * v * s⁻¹ * v⁻¹) * (w * v⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hsK _ hw) hv) (inv_mem hw)
  intro w hw
  rcases hcover w hw with h | h | h | h
  · exact mul_mem (hsK w h) (inv_mem h)
  · exact hgen h hk0
  · exact hgen h hk1
  · exact hgen h hk2

end Rotation

structure Sec38V {G : Type} [Group G] (T Q Zs V Q₀ : Subgroup G) (x z v₀ : G) : Prop where
  T_V : T ≤ normalizer (V : Set G)
  Zs_eq : Zs = V ⊓ centralizer ({x} : Set G)
  z_comm : ∀ b ∈ V, z * b = b * z
  comm_V : ∀ a ∈ V, ∀ b ∈ V, a * b * a⁻¹ * b⁻¹ ∈ Zs
  card_TC : Nat.card ↥(T ⊓ centralizer (Q : Set G)) ≤ 2
  v₀_mem : v₀ ∈ V
  v₀_not : v₀ ∉ normalizer (Q₀ : Set G)
  fpf₀ : v₀ ∉ Q₀ ⊔ Zs
  fpf₁ : v₀ * (x * v₀ * x⁻¹)⁻¹ ∉ Q₀ ⊔ Zs
  fpf₂ : v₀ * (x⁻¹ * v₀ * x)⁻¹ ∉ Q₀ ⊔ Zs
  cover : ∀ w ∈ V, w ∈ Q₀ ⊔ Zs ∨ w * v₀⁻¹ ∈ Q₀ ⊔ Zs ∨ w * (x * v₀ * x⁻¹)⁻¹ ∈ Q₀ ⊔ Zs ∨
    w * (x⁻¹ * v₀ * x)⁻¹ ∈ Q₀ ⊔ Zs

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem Zs_le_T : Zs ≤ T := by
  have hS := H.q0.dData.suz
  have hE : E ≤ P := by
    calc E = P ⊓ centralizer (E : Set G) := hS.P_cE.symm
      _ ≤ P := inf_le_left
  intro s hs
  rw [hS.Zs_eq] at hs
  have hs' : s ∈ A₁ ⊓ centerIn (E ⊔ F) := hs
  exact sup_le (hE.trans hS.P_le) hS.F_le (mem_inf.mp hs').2.1

theorem x_comm_Zs {s : G} (hs : s ∈ Zs) : x * s = s * x := by
  have hS := H.q0.dData.suz
  rw [hS.Zs_eq] at hs
  have hs' : s ∈ A₁ ⊓ centerIn (E ⊔ F) := hs
  have hx : x ∈ centerIn A₁ := by
    rw [hS.setting.center_A₁]
    exact mem_zpowers x
  exact (mem_centralizer_iff.mp hx.2 s (mem_inf.mp hs').1).symm

theorem T_conj_Zs (hTV : T ≤ normalizer (V : Set G)) (hZs : Zs = V ⊓ centralizer ({x} : Set G))
    {t : G} (ht : t ∈ T) {s : G} (hs : s ∈ Zs) : t * s * t⁻¹ ∈ Zs := by
  have hTx : T ≤ centralizer ({x} : Set G) :=
    H.q0.dData.suz.T_le.trans (map_subtype_le _ : sec3B A₁ x ≤ centralizer ({x} : Set G))
  rw [hZs] at hs ⊢
  obtain ⟨hsV, hsx⟩ := mem_inf.mp hs
  exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hTV ht) s).mp hsV,
    mul_mem (mul_mem (hTx ht) hsx) (inv_mem (hTx ht))⟩

theorem Zs_le_Q (hTV : T ≤ normalizer (V : Set G)) (hZs : Zs = V ⊓ centralizer ({x} : Set G))
    (hTC : Nat.card ↥(T ⊓ centralizer (Q : Set G)) ≤ 2) : Zs ≤ Q := by
  have hS := H.q0.dData.suz
  have hzT : z ∈ centerIn T := by
    rw [hS.T_center]
    exact mem_zpowers z
  have hz2 : Nat.card (zpowers z) = 2 := H.xsub.card_zpowers_z
  have hzZs : z ∈ Zs := hS.z_mem
  have hidx : ((zpowers z).subgroupOf Zs).index = 2 := by
    have h := Subgroup.relIndex_mul_card (zpowers z) Zs
    rw [inf_of_le_left (zpowers_le.mpr hzZs), hS.Zs_card, hz2] at h
    change (zpowers z).relIndex Zs = 2
    omega
  have hzt : ∀ t ∈ T, ∀ c ∈ zpowers z, t * c * t⁻¹ = c := by
    intro t ht c hc
    rcases H.xsub.mem_zpowers_z_iff.mp hc with h | h
    · rw [h]
      group
    · have h' : c = z := h
      rw [h', mem_centralizer_iff.mp hzT.2 t ht, mul_inv_cancel_right]
  have hcomm : ∀ t ∈ T, ∀ s ∈ Zs, t * s * t⁻¹ * s⁻¹ ∈ zpowers z := by
    intro t ht s hs
    have hts := H.T_conj_Zs hTV hZs ht hs
    have hiff : t * s * t⁻¹ ∈ zpowers z ↔ s ∈ zpowers z := by
      constructor
      · intro h
        have h1 := hzt t⁻¹ (inv_mem ht) _ h
        rw [show t⁻¹ * (t * s * t⁻¹) * t⁻¹⁻¹ = s by group] at h1
        rw [h1]
        exact h
      · intro h
        rw [hzt t ht s h]
        exact h
    have h := (mul_mem_iff_of_index_two hidx (a := ⟨t * s * t⁻¹, hts⟩) (b := (⟨s, hs⟩ : Zs)⁻¹)).mpr
      (by rw [inv_mem_iff, mem_subgroupOf, mem_subgroupOf]; exact hiff)
    exact mem_subgroupOf.mp h
  intro s hs
  let D' : XSub G := ⟨Q, z, hS.q8.1, hS.Q_center⟩
  have hsT : s ∈ T := H.Zs_le_T hs
  have hsN : s ∈ D'.N := hS.T_Q hsT
  have hρ : D'.ρ ⟨s, hsN⟩ = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨a, ha, rfl⟩ := D'.exists_cl v
    rw [D'.ρ_cl _ ha]
    change D'.cl (s * a * s⁻¹) = D'.cl a
    have haQ : a ∈ Q := ha
    rw [D'.cl_eq_cl_iff (D'.conj_mem hsN ha) ha,
      show (s * a * s⁻¹)⁻¹ * a = (a⁻¹ * s * a⁻¹⁻¹ * s⁻¹)⁻¹ by group]
    exact inv_mem (hcomm a⁻¹ (hS.Q_le (inv_mem haQ)) s hs)
  obtain ⟨c, hc, hcs⟩ := (D'.ρ_eq_one_iff _).mp hρ
  have hcQ : c ∈ Q := hc
  have hcT : c⁻¹ * s ∈ T ⊓ centralizer (Q : Set G) :=
    mem_inf.mpr ⟨mul_mem (inv_mem (hS.Q_le hcQ)) hsT, hcs⟩
  have hzle : zpowers z ≤ T ⊓ centralizer (Q : Set G) := by
    rw [zpowers_le]
    exact ⟨hzT.1, H.z_mem_centerIn_Q.2⟩
  have heq : zpowers z = T ⊓ centralizer (Q : Set G) :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hz2]; exact hTC)
  rw [← heq] at hcT
  have h2 : c⁻¹ * s ∈ Q := (zpowers_le.mpr H.z_mem_Q) hcT
  simpa using mul_mem hcQ h2

variable {v₀ : G}

theorem V_le_N (hV : Sec38V T Q Zs V Q₀ x z v₀) : V ≤ H.xsub.N := by
  have hS := H.q0.dData.suz
  have hZQ := H.Zs_le_Q hV.T_V hV.Zs_eq hV.card_TC
  have hZV : Zs ≤ V := by
    rw [hV.Zs_eq]
    exact inf_le_left
  have hK1 : Q₀ ⊔ Zs ≤ H.xsub.Q₁ := sup_le H.Q₀_le (hZQ.trans H.Q_le)
  have hxK : x ∈ normalizer ((Q₀ ⊔ Zs : Subgroup G) : Set G) := by
    have hxZ : x ∈ normalizer (Zs : Set G) := centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun s hs => (H.x_comm_Zs hs).symm)
    rw [mem_normalizer_iff_map_conj_eq] at hxZ ⊢
    rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp H.q0.x_Q₀, hxZ]
  have hVQ : ∀ q ∈ Q, ∀ w ∈ V, q * w * q⁻¹ * w⁻¹ ∈ Q₀ ⊔ Zs := by
    intro q hq
    let D' : XSub G := ⟨Q, z, hS.q8.1, hS.Q_center⟩
    have hqT : q ∈ T := hS.Q_le hq
    have hqK : q ∈ normalizer ((Q₀ ⊔ Zs : Subgroup G) : Set G) := by
      have hq₀ : q ∈ normalizer (Q₀ : Set G) :=
        centralizer_le_normalizer _ (H.Q_le_centralizer hq)
      have hqZ : q ∈ normalizer (Zs : Set G) :=
        G2.mem_normalizer_of_conj (fun s hs => H.T_conj_Zs hV.T_V hV.Zs_eq hqT hs)
          (fun s hs => by simpa using H.T_conj_Zs hV.T_V hV.Zs_eq (inv_mem hqT) hs)
      rw [mem_normalizer_iff_map_conj_eq] at hq₀ hqZ ⊢
      rw [Subgroup.map_sup, hq₀, hqZ]
    have hqq : q * q ∈ zpowers z := by
      have hqD : q ∈ D'.Q₁ := hq
      have h := (D'.cl_eq_cl_iff hqD (inv_mem hqD)).mp (D'.cl_inv hqD).symm
      rw [show q * q = (q⁻¹ * q⁻¹)⁻¹ by rw [mul_inv_rev, inv_inv]]
      exact inv_mem h
    have hs2 : ∀ w ∈ V, q * (q * w * q⁻¹) * q⁻¹ = w := by
      intro w hw
      have hc : (q * q) * w = w * (q * q) := by
        rcases H.xsub.mem_zpowers_z_iff.mp hqq with h | h
        · rw [h, one_mul, mul_one]
        · have h' : q * q = z := h
          rw [h']
          exact hV.z_comm w hw
      calc q * (q * w * q⁻¹) * q⁻¹ = (q * q) * w * (q * q)⁻¹ := by group
        _ = w * (q * q) * (q * q)⁻¹ := by rw [hc]
        _ = w := by group
    have hx3 : x * x * x = 1 := by rw [← pow_three', H.x_pow_three]
    exact comm_mem_of_rotation (V := V) (K := Q₀ ⊔ Zs) hx3
      (fun k hk => (mem_normalizer_iff.mp hxK k).mp hk)
      (fun k hk => by simpa using (mem_normalizer_iff.mp (inv_mem hxK) k).mp hk)
      (fun k hk => (mem_normalizer_iff.mp hqK k).mp hk)
      (fun w hw => (mem_normalizer_iff.mp (hV.T_V hqT) w).mp hw)
      (mem_centralizer_iff.mp H.x_mem_centralizer_Q q hq) hs2 hV.v₀_mem hV.fpf₀ hV.fpf₁
      hV.fpf₂ hV.cover
  intro v hv
  have hle : H.xsub.Q₁.map (MulAut.conj v).toMonoidHom ≤ H.xsub.Q₁ := by
    rw [xsub_Q₁, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      change v * a * v⁻¹ ∈ Q₀ ⊔ Q
      have h := hV.comm_V v hv a (H.q0.Q₀_le ha)
      rw [show v * a * v⁻¹ = (v * a * v⁻¹ * a⁻¹) * a by group]
      exact mul_mem (hZQ.trans H.Q_le h) (H.Q₀_le ha)
    · rintro _ ⟨b, hb, rfl⟩
      change v * b * v⁻¹ ∈ Q₀ ⊔ Q
      have hk := hVQ b hb v⁻¹ (inv_mem hv)
      have hkV : b * v⁻¹ * b⁻¹ * v⁻¹⁻¹ ∈ V := sup_le H.q0.Q₀_le hZV hk
      have h := hV.comm_V v hv _ hkV
      rw [show v * b * v⁻¹ = (v * (b * v⁻¹ * b⁻¹ * v⁻¹⁻¹) * v⁻¹ *
          (b * v⁻¹ * b⁻¹ * v⁻¹⁻¹)⁻¹) * (b * v⁻¹ * b⁻¹ * v⁻¹⁻¹) * b by group]
      exact mul_mem (mul_mem (hZQ.trans H.Q_le h) (hK1 hk)) (H.Q_le hb)
  have hcard : Nat.card H.xsub.Q₁ ≤ Nat.card (H.xsub.Q₁.map (MulAut.conj v).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj v).injective).ge
  exact mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle hcard)

theorem mem_normalizer_Q₀_of_map {n : H.xsub.N}
    (h : (H.xsub.clSub Q₀).map (H.ρG n : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = H.xsub.clSub Q₀) :
    (n : G) ∈ normalizer (Q₀ : Set G) :=
  H.xsub.mem_normalizer_of_map_ρ_clSub H.Q₀_le H.z_mem_Q₀ n h

theorem exists_move (hV : Sec38V T Q Zs V Q₀ x z v₀) :
    ∃ n : H.xsub.N, H.ρG n ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate ∧
      (H.xsub.clSub Q₀).map (H.ρG n : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) ≠ H.xsub.clSub Q₀ := by
  have hvN : v₀ ∈ H.xsub.N := H.V_le_N hV hV.v₀_mem
  refine ⟨⟨v₀, hvN⟩ * ⟨x, H.x_mem_N⟩ * (⟨v₀, hvN⟩ : H.xsub.N)⁻¹ *
    (⟨x, H.x_mem_N⟩ : H.xsub.N)⁻¹, ?_, ?_⟩
  ·
    let φ : H.xsub.N →* Multiplicative (ZMod 2) :=
      (dicksonHom H.xsub.q H.xsub.q_nondegenerate).comp H.xsub.ρ
    have hk : H.xsub.ρ (⟨v₀, hvN⟩ * ⟨x, H.x_mem_N⟩ * (⟨v₀, hvN⟩ : H.xsub.N)⁻¹ *
        (⟨x, H.x_mem_N⟩ : H.xsub.N)⁻¹) ∈ (dicksonHom H.xsub.q H.xsub.q_nondegenerate).ker := by
      change φ (⟨v₀, hvN⟩ * ⟨x, H.x_mem_N⟩ * (⟨v₀, hvN⟩ : H.xsub.N)⁻¹ *
        (⟨x, H.x_mem_N⟩ : H.xsub.N)⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (φ ⟨v₀, hvN⟩)]
      group
    rw [dicksonHom_ker, mem_subgroupOf] at hk
    exact hk
  · intro h
    have hn := H.mem_normalizer_Q₀_of_map h
    have hm : v₀ * x * v₀⁻¹ ∈ normalizer (Q₀ : Set G) := by
      have h1 := mul_mem hn H.q0.x_Q₀
      have e : ((⟨v₀, hvN⟩ * ⟨x, H.x_mem_N⟩ * (⟨v₀, hvN⟩ : H.xsub.N)⁻¹ *
          (⟨x, H.x_mem_N⟩ : H.xsub.N)⁻¹ : H.xsub.N) : G) * x = v₀ * x * v₀⁻¹ := by
        show v₀ * x * v₀⁻¹ * x⁻¹ * x = v₀ * x * v₀⁻¹
        group
      rwa [e] at h1
    have hφinj : Function.Injective ((MulAut.conj v₀⁻¹ : MulAut G) : G →* G) :=
      (MulAut.conj v₀⁻¹).injective
    obtain ⟨e⟩ := H.q0.Q₀_iso
    have hQ' := H.q0.unique (Q₀.map ((MulAut.conj v₀⁻¹ : MulAut G) : G →* G)) ?_ ?_
      ⟨(Q₀.equivMapOfInjective _ hφinj).symm.trans e⟩ ?_
    · apply hV.v₀_not
      have h1 : v₀⁻¹ ∈ normalizer (Q₀ : Set G) := mem_normalizer_iff_map_conj_eq.mpr hQ'
      simpa using inv_mem h1
    · rintro _ ⟨a, ha, rfl⟩
      change v₀⁻¹ * a * v₀⁻¹⁻¹ ∈ V
      exact mul_mem (mul_mem (inv_mem hV.v₀_mem) (H.q0.Q₀_le ha))
        (by rw [inv_inv]; exact hV.v₀_mem)
    · refine G2.mem_normalizer_of_conj ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        refine ⟨(v₀ * x * v₀⁻¹) * a * (v₀ * x * v₀⁻¹)⁻¹, (mem_normalizer_iff.mp hm a).mp ha, ?_⟩
        show v₀⁻¹ * ((v₀ * x * v₀⁻¹) * a * (v₀ * x * v₀⁻¹)⁻¹) * v₀⁻¹⁻¹ =
          x * (v₀⁻¹ * a * v₀⁻¹⁻¹) * x⁻¹
        group
      · rintro _ ⟨a, ha, rfl⟩
        refine ⟨(v₀ * x * v₀⁻¹)⁻¹ * a * (v₀ * x * v₀⁻¹),
          by simpa using (mem_normalizer_iff.mp (inv_mem hm) a).mp ha, ?_⟩
        show v₀⁻¹ * ((v₀ * x * v₀⁻¹)⁻¹ * a * (v₀ * x * v₀⁻¹)) * v₀⁻¹⁻¹ =
          x⁻¹ * (v₀⁻¹ * a * v₀⁻¹⁻¹) * x
        group
    · rw [Sec3.centerIn_map_of_injective _ hφinj, H.q0.center_Q₀, H.q0.dData.suz.Q_center,
        MonoidHom.map_zpowers]
      congr 1
      show v₀⁻¹ * z * v₀⁻¹⁻¹ = z
      rw [inv_inv, mul_assoc, hV.z_comm v₀ hV.v₀_mem, ← mul_assoc, inv_mul_cancel, one_mul]

end Sec38Hyp

end CFSG.ComponentClassification.AS81

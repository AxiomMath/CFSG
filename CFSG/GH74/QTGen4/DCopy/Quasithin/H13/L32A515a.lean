module

public import CFSG.Quasithin.H13.L32A515a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section V

variable {T L V V₂ : Subgroup G} [IsMulCommutative ↥V] (S14 : L32NSet14.Setting_F4 G T L V V₂)
include S14

theorem fix_V1_F4 {z g w : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hgz : g * z * g⁻¹ = z)
    (hw : w ∈ fsuV1 T V) : g * w * g⁻¹ = w := by
  rcases S14.eq_of_mem_V1_F4 hz hz1 hw with rfl | rfl
  · group
  · exact hgz

theorem p3_V_of_rot_F4 {z a c g : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) (hc : c ∈ V) (hcV : c ∉ V₂) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgz : g * z * g⁻¹ = z) (hga : g * a * g⁻¹ = c) (hgc : g * c * g⁻¹ = a * c) :
    ∀ v ∈ V, p3 g v ∈ fsuV1 T V := by
  have hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => S14.comm_V_F4 hx hy
  have haV' : a ∈ V := S14.hV2.2.1 ha
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have haa : a * a = 1 := S14.mul_self_V_F4 haV'
  have hcc : c * c = 1 := S14.mul_self_V_F4 hc
  have hzz : z * z = 1 := S14.mul_self_V_F4 hzV

  let W : Subgroup G :=
    { carrier := {v | v ∈ V ∧ p3 g v ∈ fsuV1 T V}
      one_mem' := ⟨one_mem _, by simp [p3]⟩
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [p3_mul hab hgV hx.1 hy.1]; exact mul_mem hx.2 hy.2⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
        rw [p3_inv hab hgV hx.1]; exact inv_mem hx.2⟩ }
  have hWz : z ∈ W := ⟨hzV, by
    simp only [p3, hgz]
    rw [hzz, one_mul]
    exact hz⟩
  have hWa : a ∈ W := ⟨haV', by
    have e : p3 g a = 1 := by
      simp only [p3, hga, hgc]
      calc a * c * (a * c) = a * (c * a) * c := by group
        _ = a * (a * c) * c := by rw [hab c hc a haV']
        _ = 1 := by rw [← mul_assoc, haa, one_mul, hcc]
    rw [e]
    exact one_mem _⟩
  have hWc : c ∈ W := ⟨hc, by
    have hgac : g * (a * c) * g⁻¹ = a := by
      rw [show g * (a * c) * g⁻¹ = (g * a * g⁻¹) * (g * c * g⁻¹) by group, hga, hgc,
        ← mul_assoc, hab c hc a haV', mul_assoc, hcc, mul_one]
    have e : p3 g c = 1 := by
      simp only [p3, hgc, hgac]
      calc c * (a * c) * a = c * (a * (c * a)) := by group
        _ = c * (a * (a * c)) := by rw [hab c hc a haV']
        _ = 1 := by rw [← mul_assoc a a, haa, one_mul, hcc]
    rw [e]
    exact one_mem _⟩
  intro v hv
  have hV1W : ∀ w ∈ fsuV1 T V, w ∈ W := fun w hw => by
    rcases S14.eq_of_mem_V1_F4 hz hz1 hw with rfl | rfl
    · exact one_mem _
    · exact hWz
  have hV2W : ∀ w ∈ V₂, w ∈ W := fun w hw => by
    rcases S14.mem_V2_F4 ha haV hw with h | h
    · exact hV1W w h
    · rw [show w = a⁻¹ * (a * w) by group]
      exact mul_mem (inv_mem hWa) (hV1W _ h)
  have hvW : v ∈ W := by
    rcases S14.mem_V_F4 hc hcV hv with h | h
    · exact hV2W v h
    · rw [show v = c⁻¹ * (c * v) by group]
      exact mul_mem (inv_mem hWc) (hV2W _ h)
  exact hvW.2

theorem p3_V_of_triv_F4 {z g₀ t : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hg₀V : g₀ ∈ Subgroup.normalizer (V : Set G)) (hg₀z : g₀ * z * g₀⁻¹ = z)
    (hg₀ : ∀ v ∈ V, p3 g₀ v ∈ fsuV1 T V) (ht : t ∈ L32NSet14.trivSub V (fsuV1 T V))
    (hy1 : g₀ * t ∈ Subgroup.normalizer (fsuV1 T V : Set G)) :
    ∀ v ∈ V, p3 (g₀ * t) v ∈ fsuV1 T V := by
  have hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => S14.comm_V_F4 hx hy
  have hV1V : fsuV1 T V ≤ V := inf_le_left
  have hc : ∀ v ∈ V, g₀ * v * g₀⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hg₀V v).mp hv

  have key : ∀ v ∈ V, ∃ w ∈ fsuV1 T V, g₀ * t * v * (g₀ * t)⁻¹ = w * (g₀ * v * g₀⁻¹) := by
    intro v hv
    refine ⟨t * v * t⁻¹ * v⁻¹, ht.2.2 v hv, ?_⟩
    rw [show g₀ * t * v * (g₀ * t)⁻¹ = g₀ * (t * v * t⁻¹ * v⁻¹) * g₀⁻¹ * (g₀ * v * g₀⁻¹) by group,
      fix_V1_F4 S14 hz hz1 hg₀z (ht.2.2 v hv)]
  intro v hv
  obtain ⟨w₁, hw₁, e₁⟩ := key v hv
  obtain ⟨w₂, hw₂, e₂⟩ := key _ (hc v hv)
  have hw₁' : (g₀ * t) * w₁ * (g₀ * t)⁻¹ ∈ fsuV1 T V :=
    (Subgroup.mem_normalizer_iff.mp hy1 w₁).mp hw₁
  set y := g₀ * t with hy
  set p := g₀ * v * g₀⁻¹ with hp
  set q := g₀ * p * g₀⁻¹ with hq
  have hpV : p ∈ V := hc v hv
  have hqV : q ∈ V := hc p hpV
  have e₃ : y * (y * v * y⁻¹) * y⁻¹ = (y * w₁ * y⁻¹) * (w₂ * q) := by
    rw [e₁, show y * (w₁ * p) * y⁻¹ = (y * w₁ * y⁻¹) * (y * p * y⁻¹) by group, e₂]
  have hp3 : p3 y v = (w₁ * ((y * w₁ * y⁻¹) * w₂)) * p3 g₀ v := by
    simp only [p3]
    rw [e₃, e₁, ← hp, ← hq]
    have hw₁V := hV1V hw₁
    have hw₂V := hV1V hw₂
    have hw₃V := hV1V hw₁'
    calc v * (w₁ * p) * (y * w₁ * y⁻¹ * (w₂ * q)) = (v * w₁) * p * (y * w₁ * y⁻¹) * w₂ * q := by
          group
      _ = (w₁ * v) * p * (y * w₁ * y⁻¹) * w₂ * q := by rw [hab v hv w₁ hw₁V]
      _ = w₁ * v * (p * (y * w₁ * y⁻¹)) * w₂ * q := by group
      _ = w₁ * v * ((y * w₁ * y⁻¹) * p) * w₂ * q := by rw [hab p hpV _ hw₃V]
      _ = w₁ * (v * (y * w₁ * y⁻¹)) * (p * w₂) * q := by group
      _ = w₁ * ((y * w₁ * y⁻¹) * v) * (w₂ * p) * q := by
          rw [hab v hv _ hw₃V, hab p hpV w₂ hw₂V]
      _ = w₁ * (y * w₁ * y⁻¹) * (v * w₂) * p * q := by group
      _ = w₁ * (y * w₁ * y⁻¹) * (w₂ * v) * p * q := by rw [hab v hv w₂ hw₂V]
      _ = w₁ * (y * w₁ * y⁻¹ * w₂) * (v * p * q) := by group
  rw [hp3]
  exact mul_mem (mul_mem hw₁ (mul_mem hw₁' hw₂)) (hg₀ v hv)

end V

namespace Setting147

variable {T L V H : Subgroup G}

theorem l1_trivSub_le_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) :
    l1 T L V ⊓ L32NSet14.trivSub V (fsuV1 T V) ≤ pCoreOf 2 (l1 T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hL1X : l1 T L V ≤ L32NSet14.nX T V := hl1eq ▸ S14.L1_le_X_F4
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg => ?_) (fun k => ?_)
  · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      Subgroup.mem_normalizer_fintype fun k hk =>
        L32NSet14.conj_mem_trivSub (hL1X hg).1 (hL1X hg).2 hk⟩
  · have hk2 := S14.sq_mem_cent_F4 k.2.2
    have hkL : (k : G) ∈ L := ((oTwoUpper_le _) k.2.1).1
    have hO : (k : G) ^ 2 ∈ pCoreOf 2 L := by
      rw [← S14.cent_eq_F4]
      exact ⟨L.pow_mem hkL 2, hk2⟩
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 L ⟨_, hO⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have h1 : ((k : G) ^ 2) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul]
    exact h1

theorem cent_UH_l1_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) :
    centralizerMod (fsuV1 T V) (l1 T L V) (conjClosure V H) = pCoreOf 2 (l1 T L V) := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hL1X : l1 T L V ≤ L32NSet14.nX T V := hl1eq ▸ S14.L1_le_X_F4
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hUab := Setting147.UH_comm S
  apply le_antisymm
  · rintro g ⟨hgL, hgN, hg⟩
    exact Setting147.l1_trivSub_le_F4 S h1222 h1332 h1334
      ⟨hgL, (hL1X hgL).1, hgN, fun v hv => hg v (le_conjClosure V H hv)⟩
  · intro q hq
    have hqL : q ∈ l1 T L V := pCoreOf_le 2 _ hq
    refine ⟨hqL, (hL1X hqL).2, ?_⟩
    have hqN : q ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
      le_normalizer_conjClosure V H (hL1H hqL)
    refine comm_mem_closure rfl hUab hqN ?_
    rintro _ ⟨h, hh, v, hv, rfl⟩
    have hq' : h⁻¹ * q * h ∈ pCoreOf 2 (l1 T L V) := by
      have := (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_pCoreOf 2 _ (hHL (inv_mem hh))) q).mp hq
      simpa using this
    have h1 := (S14.pCoreOf_L1_le_F4 (hl1eq ▸ hq')).2.2 v hv
    rw [show q * (h * v * h⁻¹) * q⁻¹ * (h * v * h⁻¹)⁻¹ =
      h * ((h⁻¹ * q * h) * v * (h⁻¹ * q * h)⁻¹ * v⁻¹) * h⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp (S.hz.2.1 hh) _).mp h1

theorem p3_V_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {y : G} (hy : y ∈ l1 T L V) (hyO : y ∉ pCoreOf 2 (l1 T L V)) :
    ∀ v ∈ V, p3 y v ∈ fsuV1 T V := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hL1X : l1 T L V ≤ L32NSet14.nX T V := hl1eq ▸ S14.L1_le_X_F4
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  have haV' : a ∈ V := S14.hV2.2.1 ha
  have hzV₂ : z ∈ V₂ := S14.hV2.1 hz
  have habV : a * b ∈ V := mul_mem haV' hb
  have habV₂ : a * b ∉ V₂ := fun h => hbV (by
    rw [show b = a⁻¹ * (a * b) by group]; exact mul_mem (inv_mem ha) h)
  have hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => S14.comm_V_F4 hx hy
  obtain ⟨x, hx, hxz, hxa, hxb⟩ := S14.exists_x_F4 hz hz1 ha haV hb hbV
  obtain ⟨x', hx', hx'z, hx'a, hx'b⟩ := S14.exists_x_F4 hz hz1 ha haV habV habV₂
  obtain ⟨ψ, hψ⟩ := S14.exists_rep_F4
  have hxX := S14.L1_le_X_F4 hx
  have hx'X := S14.L1_le_X_F4 hx'
  have hyX := hL1X hy

  have hψx : ψ ⟨x, hxX⟩ ≠ 1 := fun h => by
    have h1 := ((hψ _).mp h).2.2 a haV'
    rw [hxa] at h1
    apply hbV
    rw [show b = b * a⁻¹ * a by group]
    exact mul_mem (S14.hV2.1 h1) ha
  have hψy : ψ ⟨y, hyX⟩ ≠ 1 := fun h =>
    hyO (Setting147.l1_trivSub_le_F4 S h1222 h1332 h1334 ⟨hy, (hψ _).mp h⟩)
  have hψx' : ψ ⟨x', hx'X⟩ ≠ 1 := fun h => by
    have h1 := ((hψ _).mp h).2.2 a haV'
    rw [hx'a, show a * b * a⁻¹ = b by rw [hab _ haV' _ hb]; group] at h1
    exact hbV (S14.hV2.1 h1)
  have h3x := S14.cube_eq_one_F4 ψ hx
  have h3x' := S14.cube_eq_one_F4 ψ hx'
  have h3y := S14.cube_eq_one_F4 ψ (hl1eq ▸ hy)

  have hxx' : ψ ⟨x', hx'X⟩ ≠ ψ ⟨x, hxX⟩ := fun h => by
    have hk : ψ (⟨x, hxX⟩⁻¹ * ⟨x', hx'X⟩) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have ht : x⁻¹ * x' ∈ L32NSet14.trivSub V (fsuV1 T V) := by simpa using (hψ _).mp hk
    have h1 := ht.2.2 a haV'
    have e : a * b = (x⁻¹ * x' * a * (x⁻¹ * x')⁻¹ * a⁻¹) * b :=
      calc a * b = x' * a * x'⁻¹ := hx'a.symm
        _ = x * ((x⁻¹ * x') * a * (x⁻¹ * x')⁻¹ * a⁻¹) * x⁻¹ * (x * a * x⁻¹) := by group
        _ = (x⁻¹ * x' * a * (x⁻¹ * x')⁻¹ * a⁻¹) * b := by rw [fix_V1_F4 S14 hz hz1 hxz h1, hxa]
    have hw : a = x⁻¹ * x' * a * (x⁻¹ * x')⁻¹ * a⁻¹ := mul_right_cancel e
    exact haV (hw ▸ h1)

  have hcase : ψ ⟨y, hyX⟩ = ψ ⟨x, hxX⟩ ∨ ψ ⟨y, hyX⟩ = ψ ⟨x', hx'X⟩ := by
    rcases sl2_order3_cases _ _ h3x h3y hψx hψy with h | h
    · exact Or.inl h
    · right
      rcases sl2_order3_cases _ _ h3x h3x' hψx hψx' with h' | h'
      · exact absurd h' hxx'
      · rw [h, h']
  have hy1 : y ∈ Subgroup.normalizer (fsuV1 T V : Set G) := hyX.2
  rcases hcase with h | h
  · have hk : ψ (⟨x, hxX⟩⁻¹ * ⟨y, hyX⟩) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have ht : x⁻¹ * y ∈ L32NSet14.trivSub V (fsuV1 T V) := by simpa using (hψ _).mp hk
    have hrot := p3_V_of_rot_F4 S14 hz hz1 ha haV hb hbV hxX.1 hxz hxa hxb
    have hyeq : y = x * (x⁻¹ * y) := by group
    rw [hyeq] at hy1 ⊢
    exact p3_V_of_triv_F4 S14 hz hz1 hxX.1 hxz hrot ht hy1
  · have hk : ψ (⟨x', hx'X⟩⁻¹ * ⟨y, hyX⟩) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have ht : x'⁻¹ * y ∈ L32NSet14.trivSub V (fsuV1 T V) := by simpa using (hψ _).mp hk
    have hrot := p3_V_of_rot_F4 S14 hz hz1 ha haV habV habV₂ hx'X.1 hx'z hx'a hx'b
    have hyeq : y = x' * (x'⁻¹ * y) := by group
    rw [hyeq] at hy1 ⊢
    exact p3_V_of_triv_F4 S14 hz hz1 hx'X.1 hx'z hrot ht hy1

theorem p3_mem_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) {y : G}
    (hy : y ∈ l1 T L V) (hyO : y ∉ pCoreOf 2 (l1 T L V)) :
    ∀ u ∈ conjClosure V H, p3 y u ∈ fsuV1 T V := by
  have hUab := Setting147.UH_comm S
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hyN : y ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H (hL1H hy)
  intro u hu
  refine Subgroup.closure_induction (p := fun u _ => u ∈ conjClosure V H ∧ p3 y u ∈ fsuV1 T V)
    ?_ ⟨one_mem _, by simp [p3]⟩ (fun x y' _ _ hx hy' => ⟨mul_mem hx.1 hy'.1, ?_⟩)
    (fun x _ hx => ⟨inv_mem hx.1, ?_⟩) hu |>.2
  · rintro _ ⟨h, hh, v, hv, rfl⟩
    refine ⟨mem_conjClosure hh hv, ?_⟩
    have hy' : h⁻¹ * y * h ∈ l1 T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (hHL (inv_mem hh)) y).mp hy
      simpa using this
    have hyO' : h⁻¹ * y * h ∉ pCoreOf 2 (l1 T L V) := fun h' => hyO (by
      have := (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_pCoreOf 2 _ (hHL hh)) _).mp h'
      simpa [mul_assoc] using this)
    rw [p3_conj]
    exact (Subgroup.mem_normalizer_iff.mp (S.hz.2.1 hh) _).mp
      (p3_V_F4 S h1222 h1332 h1334 hy' hyO' v hv)
  · rw [p3_mul hUab hyN hx.1 hy'.1]
    exact mul_mem hx.2 hy'.2
  · rw [p3_inv hUab hyN hx.1]
    exact inv_mem hx.2

theorem cent_l1_UH_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) :
    centralizerMod (fsuV1 T V) (conjClosure V H) (l1 T L V) = fsuV1 T V := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hUab := Setting147.UH_comm S
  have hV1U : fsuV1 T V ≤ conjClosure V H :=
    (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V H)
  apply le_antisymm
  · rintro u ⟨huU, -, hu⟩
    obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
    obtain ⟨x, hx, hxz, hxa, -⟩ := S14.exists_x_F4 hz hz1 ha haV hb hbV
    have hxl : x ∈ l1 T L V := hl1eq ▸ hx
    have hxO : x ∉ pCoreOf 2 (l1 T L V) := fun h => by
      have h1 := (S14.pCoreOf_L1_le_F4 (hl1eq ▸ h)).2.2 a (S14.hV2.2.1 ha)
      rw [hxa] at h1
      apply hbV
      rw [show b = b * a⁻¹ * a by group]
      exact mul_mem (S14.hV2.1 h1) ha
    have hp := p3_mem_F4 S h1222 h1332 h1334 hHL hxl hxO u huU

    set w := x * u * x⁻¹ * u⁻¹ with hw
    have hwV : w ∈ fsuV1 T V := by
      have := inv_mem (hu x hxl)
      rw [hw]
      simpa [mul_assoc] using this
    have hxw : x * w * x⁻¹ = w := fix_V1_F4 S14 hz hz1 hxz hwV
    have hxu : x * u * x⁻¹ = w * u := by rw [hw]; group
    have hww : w * w = 1 := S14.mul_self_V_F4 (Subgroup.mem_inf.mp hwV).1
    have huu : u * u = 1 := Setting147.sq_fsuU S (fun v hv => S14.mul_self_V_F4 hv) u
      (conjClosure_mono le_rfl S.hz.2.1 huU)
    have hwu : w * u = u * w := hUab _ (hV1U hwV) _ huU
    have hx2 : x * (x * u * x⁻¹) * x⁻¹ = u := by
      rw [hxu, show x * (w * u) * x⁻¹ = (x * w * x⁻¹) * (x * u * x⁻¹) by group, hxw, hxu,
        ← mul_assoc, hww, one_mul]
    have he : p3 x u = w * u := by
      simp only [p3]
      rw [hx2, hxu]
      calc u * (w * u) * u = u * (u * w) * u := by rw [hwu]
        _ = w * u := by rw [← mul_assoc, huu, one_mul, hwu]
    rw [he] at hp
    rw [show u = w⁻¹ * (w * u) by group]
    exact mul_mem (inv_mem hwV) hp
  · intro v hv
    refine ⟨hV1U hv, Subgroup.le_normalizer hv, fun l hl => ?_⟩
    have hlN : l ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
      (S.hz.2.1 ((le_sup_left.trans S.hz.1.1) hl))
    rw [show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
    exact mul_mem hv ((Subgroup.mem_normalizer_iff.mp hlN _).mp (inv_mem hv))

end Setting147

theorem lemma14_5_15_three_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
      H ≤ Subgroup.normalizer (L32A.l1 T L V : Set G) →
      centralizerMod (fsuV1 T V) (L32A.l1 T L V) (conjClosure V H) = pCoreOf 2 (L32A.l1 T L V) ∧
        (pCoreOf 2 (L32A.l1 T L V)).relIndex (L32A.l1 T L V) = 3 ∧
        centralizerMod (fsuV1 T V) (conjClosure V H) (L32A.l1 T L V) = fsuV1 T V := by
  intro G _ _ T L V H S hHL
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have h3 := S14.Lp3_F4
  rw [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _] at h3
  exact ⟨Setting147.cent_UH_l1_F4 S h1222 h1332 h1334 hHL, h3,
    Setting147.cent_l1_UH_F4 S h1222 h1332 h1334 hHL⟩

end CFSG.Quasithin.H13.L32A

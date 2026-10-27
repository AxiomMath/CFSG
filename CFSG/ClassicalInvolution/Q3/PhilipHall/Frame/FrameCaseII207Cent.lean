module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf7C207
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf36Outer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open Out
open scoped commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

theorem oddCore_le_trivialOnQuot {L X : Subgroup G} (hLX : L ≤ X)
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) : oddCoreOf X ≤ trivialOnQuot L := by
  intro x hx
  have hxX : x ∈ X := oddCoreOf_le_self X hx
  refine ⟨hXN hxX, fun y hy => ?_⟩
  have hyX : y ∈ X := hLX hy
  have h1 : ⁅x, y⁆ ∈ oddCoreOf X := by
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    refine (oddCoreOf X).mul_mem hx ?_
    have := conj_mem_oddCoreIn_of_mem_normalizer (Subgroup.le_normalizer hyX)
      ((oddCoreOf X).inv_mem hx)
    simpa [oddCoreIn_eq_oddCoreOf] using this
  have h2 : ⁅x, y⁆ ∈ L := by
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by
      simp [commutatorElement_def]
    rw [e]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXN hxX) y).mp hy) (L.inv_mem hy)
  rw [oddCoreIn_eq_oddCoreOf]
  exact Out.oddCoreOf_inf_le hLX ⟨h1, h2⟩

theorem mem_trivialOnQuot_of_cmo {L M : Subgroup G} (hLM : L ≤ M) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hx : ∀ m ∈ M, ⁅x, m⁆ ∈ oddCoreOf M) :
    x ∈ trivialOnQuot L := by
  refine ⟨hxL, fun y hy => ?_⟩
  have h1 : ⁅x, y⁆ ∈ oddCoreOf M := hx y (hLM hy)
  have h2 : ⁅x, y⁆ ∈ L := by
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by
      simp [commutatorElement_def]
    rw [e]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxL y).mp hy) (L.inv_mem hy)
  rw [oddCoreIn_eq_oddCoreOf]
  exact Out.oddCoreOf_inf_le hLM ⟨h1, h2⟩

theorem innerOn_of_trivialOnQuot {L : Subgroup G} {x : G} (hx : x ∈ trivialOnQuot L) :
    InnerOn L x := by
  refine ⟨1, L.one_mem, fun y hy => ?_⟩
  have := hx.2 y hy
  rw [oddCoreIn_eq_oddCoreOf] at this
  simpa [commutatorElement_def, mul_assoc] using this

omit [Finite G] in
theorem comm_mem_of_odd_of_mem_sup_zpowers {O : Subgroup G} {b u z : G} {n : ℕ} (hn : Odd n)
    (hbn : b ^ n = 1) (hz2 : z * z = 1) (hzO : z ∉ O) (hzb : z * b = b * z)
    (hbO : b ∈ Subgroup.normalizer (O : Set G)) (hzN : z ∈ Subgroup.normalizer (O : Set G))
    (hc : b * u * b⁻¹ * u⁻¹ ∈ O ⊔ Subgroup.zpowers z) : ⁅u, b⁆ ∈ O := by
  have hzle : Subgroup.zpowers z ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.mpr hzN
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left O _ hzle] at hc
  obtain ⟨o, ho, w, hw, hcw⟩ := hc
  have hcw' : o * w = b * u * b⁻¹ * u⁻¹ := hcw
  have ho' : o ∈ O := ho
  have hw' : w = 1 ∨ w = z := eq_one_or_eq_of_mem_zpowers hz2 hw
  have hinv : ⁅u, b⁆ = (b * u * b⁻¹ * u⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rcases hw' with h | h
  · rw [h, mul_one] at hcw'
    rw [hinv, ← hcw']
    exact O.inv_mem ho'
  · exfalso
    rw [h] at hcw'
    have hbu : b * u * b⁻¹ = o * z * u := by
      calc b * u * b⁻¹ = (b * u * b⁻¹ * u⁻¹) * u := by group
        _ = o * z * u := by rw [← hcw']
    have key : ∀ k : ℕ, ∃ o' ∈ O, b ^ k * u * (b ^ k)⁻¹ = o' * z ^ k * u := by
      intro k
      induction k with
      | zero => exact ⟨1, O.one_mem, by simp⟩
      | succ k ih =>
        obtain ⟨o', ho'', he⟩ := ih
        have hbo : b * o' * b⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hbO o').mp ho''
        have hzk : z ^ k * o * (z ^ k)⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hzN k) o).mp ho'
        have hbz : b * z ^ k * b⁻¹ = z ^ k := by
          have hc' : Commute b z := hzb.symm
          exact mul_inv_eq_iff_eq_mul.mpr (hc'.pow_right k).eq
        refine ⟨(b * o' * b⁻¹) * (z ^ k * o * (z ^ k)⁻¹), O.mul_mem hbo hzk, ?_⟩
        calc b ^ (k + 1) * u * (b ^ (k + 1))⁻¹ = b * (b ^ k * u * (b ^ k)⁻¹) * b⁻¹ := by
              rw [pow_succ']; group
          _ = (b * o' * b⁻¹) * (b * z ^ k * b⁻¹) * (b * u * b⁻¹) := by rw [he]; group
          _ = (b * o' * b⁻¹) * z ^ k * (o * z * u) := by rw [hbz, hbu]
          _ = (b * o' * b⁻¹) * (z ^ k * o * (z ^ k)⁻¹) * z ^ (k + 1) * u := by
              rw [pow_succ]; group
    obtain ⟨o', ho'', he⟩ := key n
    rw [hbn] at he
    have hzn : z ^ n = o'⁻¹ := by
      have h1 : u = o' * z ^ n * u := by simpa using he
      have h2 : o' * z ^ n = 1 := by
        have := congrArg (fun y => y * u⁻¹) h1
        simpa using this.symm
      exact eq_inv_of_mul_eq_one_right h2
    obtain ⟨k, rfl⟩ := hn
    have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
    have : z ^ (2 * k + 1) = z := by rw [pow_succ, pow_mul, hz2', one_pow, one_mul]
    rw [this] at hzn
    exact hzO (hzn ▸ O.inv_mem ho'')

end Generic

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section C207

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem exists_central_mul_oddCore' {k' : G} (hk' : k' ∈ K') (htr : k' ∈ trivialOnQuot K') :
    ∃ c : G, (c = 1 ∨ c = z) ∧ ∃ n ∈ oddCoreOf K', k' = c * n := by
  obtain ⟨g, hg, hgK⟩ := d.swap
  have hk₀ : g⁻¹ * k' * g ∈ K := conj_swap_K' d hg hgK hk'
  have htr₀ : g⁻¹ * k' * g ∈ trivialOnQuot K := by
    refine ⟨conj_swap_mem_normalizer d hg hgK htr.1, fun y hy => ?_⟩
    have hyK' : g * y * g⁻¹ ∈ K' := by
      rw [← hgK]; exact conj_mem_conjSub hy
    have h1 := htr.2 _ hyK'
    rw [oddCoreIn_eq_oddCoreOf] at h1 ⊢
    have h2 : g⁻¹ * ⁅k', g * y * g⁻¹⁆ * g ∈ oddCoreOf K := by
      have : ⁅k', g * y * g⁻¹⁆ ∈ conjSub g (oddCoreOf K) := by
        rw [← Thompson.oddCoreOf_conjSub_eq, hgK]; exact h1
      rw [mem_conjSub_iff] at this
      exact this
    have e : g⁻¹ * ⁅k', g * y * g⁻¹⁆ * g = ⁅g⁻¹ * k' * g, y⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e] at h2
  obtain ⟨c, hc, n, hn, he⟩ := exists_central_mul_oddCore d hk₀ htr₀
  refine ⟨c, hc, g * n * g⁻¹, ?_, ?_⟩
  · rw [← hgK, Thompson.oddCoreOf_conjSub_eq]
    exact conj_mem_conjSub hn
  · have hgc : g * c * g⁻¹ = c := by
      rcases hc with h | h
      · rw [h]; group
      · rw [h]
        have := Subgroup.mem_centralizer_singleton_iff.mp hg
        calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [this]
          _ = z := by group
    calc k' = g * (g⁻¹ * k' * g) * g⁻¹ := by group
      _ = g * (c * n) * g⁻¹ := by rw [he]
      _ = (g * c * g⁻¹) * (g * n * g⁻¹) := by group
      _ = c * (g * n * g⁻¹) := by rw [hgc]

theorem oddCore_le_oddX {L : Subgroup G} (hLX : L ≤ sec20X (CoreAssembly.conjClass K) z K K')
    (hXN : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.normalizer (L : Set G)) :
    oddCoreOf L ≤ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') :=
  le_oddCoreOf_of_normalizes ((oddCoreOf_le_self L).trans hLX)
    (fun x hx => mem_normalizer_oddCore_of_mem_normalizer (hXN hx)) (oddCoreOf_odd_natCard L)

theorem cmoX_mem (hC : Frame203Cent) {x : G}
    (hxX : x ∈ sec20X (CoreAssembly.conjClass K) z K K')
    (hx : ∀ m ∈ K ⊔ K', ⁅x, m⁆ ∈ oddCoreOf (K ⊔ K')) :
    x ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ Subgroup.zpowers z := by
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := frameX_le_N d
  have hXN' : X ≤ Subgroup.normalizer (K' : Set G) := fun y hy =>
    ((sec20X_le_normalizers_frame d) hy).2
  have htK : x ∈ trivialOnQuot K := mem_trivialOnQuot_of_cmo le_sup_left (hXN hxX) hx
  have htK' : x ∈ trivialOnQuot K' := mem_trivialOnQuot_of_cmo le_sup_right (hXN' hxX) hx
  have hmem := hC G K K' J S R R' W V z t d x hxX (innerOn_of_trivialOnQuot htK)
    (innerOn_of_trivialOnQuot htK')
  have hMN : K ⊔ K' ≤ Subgroup.normalizer (oddCoreOf X : Set G) := fun m hm =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (le_sec20X_pair hm))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hMN] at hmem
  obtain ⟨o, ho, m, hm, rfl⟩ := hmem
  have hoK : o ∈ trivialOnQuot K := oddCore_le_trivialOnQuot le_sec20X_left hXN ho
  have hoK' : o ∈ trivialOnQuot K' := oddCore_le_trivialOnQuot le_sec20X_right hXN' ho
  have hmK : m ∈ trivialOnQuot K := by
    have : m = o⁻¹ * (o * m) := by group
    rw [this]; exact (trivialOnQuot K).mul_mem ((trivialOnQuot K).inv_mem hoK) htK
  have hmK' : m ∈ trivialOnQuot K' := by
    have : m = o⁻¹ * (o * m) := by group
    rw [this]; exact (trivialOnQuot K').mul_mem ((trivialOnQuot K').inv_mem hoK') htK'
  have hm' : m ∈ ((K ⊔ K' : Subgroup G) : Set G) := hm
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K K' d.late_K_le] at hm'
  obtain ⟨k, hk, k', hk', rfl⟩ := hm'
  have hkK : k ∈ trivialOnQuot K := by
    have : k = (k * k') * k'⁻¹ := by group
    rw [this]
    exact (trivialOnQuot K).mul_mem hmK ((trivialOnQuot K).inv_mem (le_trivialOnQuot_K d hk'))
  have hk'K' : k' ∈ trivialOnQuot K' := by
    have : k' = k⁻¹ * (k * k') := by group
    rw [this]
    exact (trivialOnQuot K').mul_mem ((trivialOnQuot K').inv_mem (le_trivialOnQuot_K' d hk)) hmK'
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_central_mul_oddCore d hk hkK
  obtain ⟨c', hc', n', hn', rfl⟩ := exists_central_mul_oddCore' d hk' hk'K'
  have hnX : n ∈ oddCoreOf X := oddCore_le_oddX d le_sec20X_left hXN hn
  have hn'X : n' ∈ oddCoreOf X := oddCore_le_oddX d le_sec20X_right hXN' hn'
  have hcz : c ∈ Subgroup.zpowers z := by
    rcases hc with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have hc'z : c' ∈ Subgroup.zpowers z := by
    rcases hc' with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have hcc : ∀ {c₀ y : G}, (c₀ = 1 ∨ c₀ = z) → y ∈ K ⊔ K' → c₀ * y = y * c₀ := by
    intro c₀ y hc₀ hy
    exact (sq_comm_of_one_or_z d hc₀).2 y hy
  have hn'M : n' ∈ K ⊔ K' := Subgroup.mem_sup_right (oddCoreOf_le_self K' hn')
  have e : o * (c * n * (c' * n')) = (o * n * n') * (c * c') := by
    have h1 : c * n * (c' * n') = c * n * (n' * c') := by rw [hcc hc' hn'M]
    have h2 : c * n = n * c := hcc hc (Subgroup.mem_sup_left (oddCoreOf_le_self K hn))
    have h3 : c * n' = n' * c := hcc hc hn'M
    calc o * (c * n * (c' * n')) = o * (c * n * (n' * c')) := by rw [h1]
      _ = o * ((n * c) * n' * c') := by rw [h2]; group
      _ = o * (n * (c * n') * c') := by group
      _ = o * (n * (n' * c) * c') := by rw [h3]
      _ = (o * n * n') * (c * c') := by group
  show o * (c * n * (c' * n')) ∈ _
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((oddCoreOf X).mul_mem
    ((oddCoreOf X).mul_mem ho hnX) hn'X)) (Subgroup.mem_sup_right (Subgroup.mul_mem _ hcz hc'z))

end C207

theorem concl20_7_of_cent (hC : Frame203Cent) {G : Type} [Group G] [Finite G] [FrameCore G]
    {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}
    (d : Std20Frame K K' J S R R' W V z t) (c5 : Concl20_5 S K K' z) : Concl20_7 S K K' z := by
  show centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr d.z_mem_cent)
  intro u hu
  suffices hL : u ∈ centralizerModOdd (S : Subgroup G)
      (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) by
    rw [c5] at hL
    exact hL
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  set M := K ⊔ K' with hM
  set L := M ⊔ sec20O2 X with hL
  obtain ⟨huS, huM, huOM, hucomm⟩ := hu
  have hCz := d.sup_le_centralizer_z
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) :=
    sec20X_le_centralizer (le_sup_left.trans hCz) (le_sup_right.trans hCz)
  have hMX : M ≤ X := le_sec20X_pair
  have hO2X : sec20O2 X ≤ X := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hLX : L ≤ X := sup_le hMX hO2X
  have huX : u ∈ Subgroup.normalizer (X : Set G) :=
    le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins (d.hSz huS)
  have huOX : u ∈ Subgroup.normalizer (oddCoreOf X : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer huX
  have huU : u ∈ centralizerModOdd ⊤ M := ⟨Subgroup.mem_top u, huM, huOM, hucomm⟩
  have hzX : z ∈ X := hMX (Subgroup.mem_sup_left d.viol.hzK.mem)
  have hzO : z ∉ oddCoreOf X := by
    intro h
    have h1 : orderOf z ∣ Nat.card (oddCoreOf X) := Subgroup.orderOf_dvd_natCard _ h
    have h2 : orderOf z = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact d.viol.hzK.sq) d.viol.hzK.ne_one
    rw [h2] at h1
    exact (Nat.not_even_iff_odd.mpr ((oddCoreOf_odd_natCard X).of_dvd_nat h1)) even_two
  have hodd : ∀ b ∈ X, Odd (orderOf b) → ⁅u, b⁆ ∈ oddCoreOf X := by
    intro b hbX hbo
    have hbN : b ∈ Subgroup.normalizer (M : Set G) :=
      le_normalizer_sup_pair d.hyp.conjInvariant d.viol.hzK d.twins d.ne (hXz hbX)
    have h1 : b * u * b⁻¹ ∈ centralizerModOdd ⊤ M := by
      have := late_cmo_conj_mem huU b
      rwa [conjSub_eq_self_of_mem (Subgroup.mem_top b),
        mem_normalizer_iff_conjSub_eq.mp hbN] at this
    have h2 : b * u * b⁻¹ * u⁻¹ ∈ centralizerModOdd ⊤ M :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ huU)
    have h3 : b * u * b⁻¹ * u⁻¹ ∈ X := by
      have hu' : u * b⁻¹ * u⁻¹ ∈ X := by
        have : u * b⁻¹ * u⁻¹ ∈ conjSub u X := conj_mem_conjSub (X.inv_mem hbX)
        rwa [mem_normalizer_iff_conjSub_eq.mp huX] at this
      have e : b * u * b⁻¹ * u⁻¹ = b * (u * b⁻¹ * u⁻¹) := by group
      rw [e]
      exact X.mul_mem hbX hu'
    have h4 := cmoX_mem d hC h3 h2.2.2.2
    exact comm_mem_of_odd_of_mem_sup_zpowers hbo (pow_orderOf_eq_one b) d.viol.hzK.sq hzO
      ((Subgroup.mem_centralizer_singleton_iff.mp (hXz hbX)).symm)
      (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hbX))
      (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hzX)) h4
  have hMu : conjSub u M = M := mem_normalizer_iff_conjSub_eq.mp huM
  have huL : u ∈ Subgroup.normalizer (L : Set G) := by
    apply Asc77.T3CII.mem_normalizer_of_conjSub_le
    rw [hL, conjSub_sup', hMu]
    exact sup_le_sup_left (conjSub_sec20O2_le huX) M
  have huOL : u ∈ Subgroup.normalizer (oddCoreOf L : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer huL
  refine ⟨huS, huL, huOL, fun l hl => ?_⟩
  have hLN : ∀ g ∈ L, g ∈ Subgroup.normalizer (oddCoreOf L : Set G) := fun g hg =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hOMX : ∀ g ∈ X, g ∈ Subgroup.normalizer (M : Set G) := fun g hg =>
    le_normalizer_sup_pair d.hyp.conjInvariant d.viol.hzK d.twins d.ne (hXz hg)
  have hOML : oddCoreOf M ≤ oddCoreOf L :=
    AscFusion.le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self M).trans le_sup_left)
      (fun g hg => mem_normalizer_oddCore_of_mem_normalizer (hOMX g (hLX hg)))
      (oddCoreOf_odd_natCard M)
  have hOXL : oddCoreOf X ⊓ L ≤ oddCoreOf L := by
    refine AscFusion.le_oddCoreOf_of_normal_odd inf_le_right ?_
      ((oddCoreOf_odd_natCard X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    intro g hg
    exact late_mem_normalizer_inf (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer (hLX hg))) (Subgroup.le_normalizer hg)
  let T : Subgroup G :=
    { carrier := {x | x ∈ L ∧ ⁅u, x⁆ ∈ oddCoreOf L}
      one_mem' := ⟨L.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxL, hx⟩ ⟨hyL, hy⟩
        refine ⟨L.mul_mem hxL hyL, ?_⟩
        have e : ⁅u, x * y⁆ = ⁅u, x⁆ * (x * ⁅u, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (oddCoreOf L).mul_mem hx
          ((Subgroup.mem_normalizer_iff.mp (hLN x hxL) _).mp hy)
      inv_mem' := by
        rintro x ⟨hxL, hx⟩
        refine ⟨L.inv_mem hxL, ?_⟩
        have e : ⁅u, x⁻¹⁆ = x⁻¹ * ⁅u, x⁆⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.mp (hLN x⁻¹ (L.inv_mem hxL)) (⁅u, x⁆⁻¹)).mp
          ((oddCoreOf L).inv_mem hx)
        rw [inv_inv] at this
        exact this }
  have hMT : M ≤ T := fun m hm =>
    ⟨Subgroup.mem_sup_left hm, hOML (hucomm m hm)⟩
  have hO2T : sec20O2 X ≤ T := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro b ⟨hbX, hbo⟩
    have hbL : b ∈ L := Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hbX, hbo⟩)
    refine ⟨hbL, hOXL ⟨hodd b hbX hbo, ?_⟩⟩
    have hub : u * b * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp huL b).mp hbL
    have e : ⁅u, b⁆ = (u * b * u⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact L.mul_mem hub (L.inv_mem hbL)
  exact (sup_le hMT hO2T hl).2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

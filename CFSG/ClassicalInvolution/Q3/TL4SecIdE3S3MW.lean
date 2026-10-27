module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3MC
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3P

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem secIdE3S3M12Center_proved :
    SecIdE3S3M12Center :=
  fun _ _ _ _ _ _ hm _ hO2 hY he => E3S3MC.center_eq_bot_of_datum hm.datum hm.cls.1 hO2 hY he

end CFSG.ClassicalInvolution.Q3.TL4
